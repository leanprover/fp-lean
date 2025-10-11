import ExampleSupport
import Examples.Classes
import Examples.Monads.Class


-- ANCHOR: MythicalCreature
structure MythicalCreature where
  large : Bool
deriving Repr
-- ANCHOR_END: MythicalCreature

-- ANCHOR: MythicalCreatureMore
section
open MythicalCreature
example := mk
end
-- ANCHOR_END: MythicalCreatureMore


-- ANCHOR: Monster
structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr
-- ANCHOR_END: Monster


/-- info:
MythicalCreature.mk (large : Bool) : MythicalCreature
-/
#check_msgs in
-- ANCHOR: MythicalCreatureMk
#check MythicalCreature.mk
-- ANCHOR_END: MythicalCreatureMk

/-- info:
MythicalCreature.large (self : MythicalCreature) : Bool
-/
#check_msgs in
-- ANCHOR: MythicalCreatureLarge
#check MythicalCreature.large
-- ANCHOR_END: MythicalCreatureLarge


/-- info:
Monster.mk (toMythicalCreature : MythicalCreature) (vulnerability : String) : Monster
-/
#check_msgs in
-- ANCHOR: MonsterMk
#check Monster.mk
-- ANCHOR_END: MonsterMk

-- ANCHOR: MonsterToCreature
example : Monster → MythicalCreature := Monster.toMythicalCreature
-- ANCHOR_END: MonsterToCreature


-- ANCHOR: Helper
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr
-- ANCHOR_END: Helper


-- ANCHOR: troll
def troll : Monster where
  large := true
  vulnerability := "sunlight"
-- ANCHOR_END: troll

/-- info:
troll.toMythicalCreature : MythicalCreature
-/
#check_msgs in
-- ANCHOR: checkTrollCast
#check troll.toMythicalCreature
-- ANCHOR_END: checkTrollCast


/-- info:
{ large := true }
-/
#check_msgs in
-- ANCHOR: evalTrollCast
#eval troll.toMythicalCreature
-- ANCHOR_END: evalTrollCast

namespace Blurble
-- ANCHOR: troll2
def troll : Monster := {large := true, vulnerability := "sunlight"}
-- ANCHOR_END: troll2
end Blurble


namespace Foo
discarding
/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  MythicalCreature
in the application
  Monster.mk true
-/
#check_msgs in
-- ANCHOR: wrongTroll1
def troll : Monster := ⟨true, "sunlight"⟩
-- ANCHOR_END: wrongTroll1
stop discarding

-- ANCHOR: troll3
def troll : Monster := ⟨⟨true⟩, "sunlight"⟩
-- ANCHOR_END: troll3
end Foo


/--
error: Application type mismatch: The argument
  troll
has type
  Monster
but is expected to have type
  MythicalCreature
in the application
  MythicalCreature.large troll
-/
#check_msgs in
-- ANCHOR: trollLargeNoDot
#eval MythicalCreature.large troll
-- ANCHOR_END: trollLargeNoDot


structure Aaa where
  a : Bool

structure Bbb where
  a : Bool
  b : String

structure Ccc extends Aaa, Bbb where


#check Monster.toMythicalCreature


-- ANCHOR: elf
def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"
-- ANCHOR_END: elf


-- ANCHOR: MonstrousAssistant
structure MonstrousAssistant extends Monster, Helper where
deriving Repr
-- ANCHOR_END: MonstrousAssistant

-- ANCHOR: MonstrousAssistantMore
example := MonstrousAssistant.toMonster
example := MonstrousAssistant.toHelper
example := Hashable
-- ANCHOR_END: MonstrousAssistantMore


/-- info:
MonstrousAssistant.mk (toMonster : Monster) (assistance payment : String) : MonstrousAssistant
-/
#check_msgs in
-- ANCHOR: checkMonstrousAssistantMk
#check MonstrousAssistant.mk
-- ANCHOR_END: checkMonstrousAssistantMk



/-- info:
MonstrousAssistant.toHelper (self : MonstrousAssistant) : Helper
-/
#check_msgs in
-- ANCHOR: checkMonstrousAssistantToHelper
#check MonstrousAssistant.toHelper
-- ANCHOR_END: checkMonstrousAssistantToHelper


/-- info:
@[reducible] def MonstrousAssistant.toHelper : MonstrousAssistant → Helper :=
fun self => { toMythicalCreature := self.toMythicalCreature, assistance := self.assistance, payment := self.payment }
-/
#check_msgs in
-- ANCHOR: printMonstrousAssistantToHelper
#print MonstrousAssistant.toHelper
-- ANCHOR_END: printMonstrousAssistantToHelper

-- ANCHOR: domesticatedTroll
def domesticatedTroll : MonstrousAssistant where
  large := true
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"
-- ANCHOR_END: domesticatedTroll

-- ANCHOR: SizedCreature
inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large
-- ANCHOR_END: SizedCreature

-- ANCHOR: nonsenseCreature
def nonsenseCreature : SizedCreature where
  large := false
  size := .large
-- ANCHOR_END: nonsenseCreature


-- ANCHOR: sizesMatch
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)
-- ANCHOR_END: sizesMatch


-- ANCHOR: huldresize
def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by
  decide
-- ANCHOR_END: huldresize

-- ANCHOR: small
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
-- ANCHOR_END: small

-- ANCHOR: smallTroll
example : (
troll.small
) = (
false
) := rfl
-- ANCHOR_END: smallTroll


/--
error: Application type mismatch: The argument
  troll
has type
  Monster
but is expected to have type
  MythicalCreature
in the application
  MythicalCreature.small troll
-/
#check_msgs in
-- ANCHOR: smallTrollWrong
example := MythicalCreature.small troll
-- ANCHOR_END: smallTrollWrong

#eval nisse.small


/--
error: Application type mismatch: The argument
  nisse
has type
  Helper
but is expected to have type
  MythicalCreature
in the application
  MythicalCreature.small nisse
-/
#check_msgs in
-- ANCHOR: smallElfNoDot
#eval MythicalCreature.small nisse
-- ANCHOR_END: smallElfNoDot

namespace VariousTypes

variable {f : Type → Type}
variable {m : Type → Type}
variable [instF : Applicative f]
variable [instM : Monad m]
variable {α : Type}
variable {β : Type}
variable {E1 : f (α → β)}
variable {E2 : f α}

-- ANCHOR: pureType
example : {α : Type} → α → f α := pure
-- ANCHOR_END: pureType

-- ANCHOR: seqType
example : f (α → β) → (Unit → f α) → f β := Seq.seq
-- ANCHOR_END: seqType

-- ANCHOR: seqSugar
example : (
E1 <*> E2
) = (
Seq.seq E1 (fun () => E2)
) := rfl
-- ANCHOR_END: seqSugar

-- ANCHOR: bindType
section
open Monad
example : m α → (α → m β) → m β := bind
end
-- ANCHOR_END: bindType


end VariousTypes

namespace OwnInstances

-- ANCHOR: ApplicativeOption
instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()
-- ANCHOR_END: ApplicativeOption

-- ANCHOR: ApplicativeExcept
instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok g => g <$> x ()
-- ANCHOR_END: ApplicativeExcept

-- ANCHOR: ApplicativeReader
instance : Applicative (Reader ρ) where
  pure x := fun _ => x
  seq f x :=
    fun env =>
      f env (x () env)
-- ANCHOR_END: ApplicativeReader

-- ANCHOR: ApplicativeId
instance : Applicative Id where
  pure x := x
  seq f x := f (x ())
-- ANCHOR_END: ApplicativeId

end OwnInstances

-- ANCHOR: somePlus
example : Option (Nat → Nat → Nat) := some Plus.plus
-- ANCHOR_END: somePlus

-- ANCHOR: somePlusFour
example : Option (Nat → Nat) := some Plus.plus <*> some 4
-- ANCHOR_END: somePlusFour

-- ANCHOR: somePlusFourSeven
example : Option Nat := some Plus.plus <*> some 4 <*> some 7
-- ANCHOR_END: somePlusFourSeven



structure NotApplicative (α : Type) where
  impossible : Empty

instance : Functor NotApplicative where
  map _ x := ⟨x.impossible⟩

instance : LawfulFunctor NotApplicative where
  id_map x := nomatch x.impossible
  map_const := by
    simp [Functor.map, Functor.mapConst]
  comp_map g h x := nomatch x.impossible



-- ANCHOR: Pair
structure Pair (α β : Type) : Type where
  first : α
  second : β
-- ANCHOR_END: Pair

-- ANCHOR: PairType
example : Type → Type → Type := Pair
-- ANCHOR_END: PairType


-- ANCHOR: FunctorPair
instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩
-- ANCHOR_END: FunctorPair

namespace CheckFunctorPair
variable {α : Type}
variable {β : Type}
variable {γ : Type}
variable {δ : Type}
variable {x : α}
variable {y : β}
variable {f : γ → δ}
variable {g : β → γ}

evaluation steps {{{ checkPairMapId }}}
-- ANCHOR: checkPairMapId
id <$> Pair.mk x y
===>
Pair.mk x (id y)
===>
Pair.mk x y
-- ANCHOR_END: checkPairMapId
end evaluation steps

-- ANCHOR: ApplicativePair
example := Applicative (Pair α)
example := Empty
-- ANCHOR_END: ApplicativePair


evaluation steps {{{ checkPairMapComp1 }}}
-- ANCHOR: checkPairMapComp1
f <$> g <$> Pair.mk x y
===>
f <$> Pair.mk x (g y)
===>
Pair.mk x (f (g y))
-- ANCHOR_END: checkPairMapComp1
end evaluation steps

evaluation steps {{{ checkPairMapComp2 }}}
-- ANCHOR: checkPairMapComp2
(f ∘ g) <$> Pair.mk x y
===>
Pair.mk x ((f ∘ g) y)
===>
Pair.mk x (f (g y))
-- ANCHOR_END: checkPairMapComp2
end evaluation steps


end CheckFunctorPair

instance : LawfulFunctor (Pair α) where
  id_map x := by
    simp [Functor.map]
  map_const := by
    simp [Functor.mapConst, Functor.map]
  comp_map g h x := by
    cases x
    simp [Function.comp, Functor.map]

discarding
/-- error:
don't know how to synthesize placeholder
context:
β α : Type
x : β
⊢ Pair α β
-/
#check_msgs in
-- ANCHOR: Pairpure
def Pair.pure (x : β) : Pair α β := _
-- ANCHOR_END: Pairpure
stop discarding


/-- error:
don't know how to synthesize placeholder for argument 'first'
context:
β α : Type
x : β
⊢ α
-/
#check_msgs in
-- ANCHOR: Pairpure2
def Pair.pure (x : β) : Pair α β := Pair.mk _ x
-- ANCHOR_END: Pairpure2

namespace ApplicativeOptionLaws

variable {α : Type}
variable {β : Type}
variable {γ : Type}
variable {δ : Type}

variable {x : α}
variable {g : α → β}
variable {f : β → γ}

evaluation steps {{{ OptionHomomorphism1 }}}
-- ANCHOR: OptionHomomorphism1
some (· ∘ ·) <*> some f <*> some g <*> some x
===>
some (f ∘ ·) <*> some g <*> some x
===>
some (f ∘ g) <*> some x
===>
some ((f ∘ g) x)
===>
some (f (g x))
-- ANCHOR_END: OptionHomomorphism1
end evaluation steps

-- ANCHOR: OptionHomomorphism
example : some (· ∘ ·) <*> some f <*> some g <*> some x = some f <*> (some g <*> some x) := by rfl
-- ANCHOR_END: OptionHomomorphism

evaluation steps {{{ OptionHomomorphism2 }}}
-- ANCHOR: OptionHomomorphism2
some f <*> (some g <*> some x)
===>
some f <*> (some (g x))
===>
some (f (g x))
-- ANCHOR_END: OptionHomomorphism2
end evaluation steps


end ApplicativeOptionLaws

namespace ApplicativeOptionLaws2

variable {α : Type}
variable {β : Type}

variable {x : α}
variable {y : α}
variable {f : α → β}

evaluation steps {{{ OptionPureSeq }}}
-- ANCHOR: OptionPureSeq
some f <*> some x
===>
f <$> some x
===>
some (f x)
-- ANCHOR_END: OptionPureSeq
end evaluation steps

-- ANCHOR: OptionPureSeq2
example : some (fun g => g x) <*> some f = some (f x) := by rfl
-- ANCHOR_END: OptionPureSeq2

end ApplicativeOptionLaws2



namespace ApplicativeToFunctor

-- ANCHOR: ApplicativeMap
def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x
-- ANCHOR_END: ApplicativeMap

-- ANCHOR: names
example := Prod
example := Nat
example := Int
-- ANCHOR_END: names

-- ANCHOR: ApplicativeExtendsFunctorOne
class Applicative (f : Type → Type) extends Functor f where
  pure : α → f α
  seq : f (α → β) → (Unit → f α) → f β
  map g x := seq (pure g) (fun () => x)
-- ANCHOR_END: ApplicativeExtendsFunctorOne

variable [_root_.Applicative F] [LawfulApplicative F] {x : F α} {f : β → γ} {g : α → β}
-- ANCHOR: AppToFunTerms
example : id <$> x = x := by simp
example : map (f ∘ g) x = map f (map g x) := by
  unfold map
  show pure (f ∘ g) <*> x = pure f <*> (pure g <*> x)
  suffices pure (· ∘ ·) <*> pure f <*> pure g <*> x = pure f <*> (pure g <*> x) by
    rw [← this]; congr; simp
  simp [LawfulApplicative.seq_assoc]
-- ANCHOR_END: AppToFunTerms


end ApplicativeToFunctor

namespace MonadApplicative


-- ANCHOR: MonadSeq
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)
-- ANCHOR_END: MonadSeq

end MonadApplicative

namespace MonadApplicativeDesugar
-- ANCHOR: MonadSeqDesugar
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  f >>= fun g =>
  x () >>= fun y =>
  pure (g y)
-- ANCHOR_END: MonadSeqDesugar

end MonadApplicativeDesugar

equational steps  {{{ testEq }}}
-- ANCHOR: testEq
1 + 1
={
/-- Foo of `plus` and `stuff` -/
}=
2
-- ANCHOR_END: testEq
stop equational steps

namespace MonadApplicativeProof1
variable {m : Type → Type}
variable [instM : Monad m]
variable [instLM : LawfulMonad m]
variable {α : Type}
variable {v : m α}

equational steps  {{{ mSeqRespId }}}
-- ANCHOR: mSeqRespId
pure id >>= fun g => v >>= fun y => pure (g y)
={
/-- `pure` is a left identity of `>>=` -/
by simp [LawfulMonad.pure_bind]
}=
v >>= fun y => pure (id y)
={
/-- Reduce the call to `id` -/
}=
v >>= fun y => pure y
={
/-- `fun x => f x` is the same as `f` -/
by
  have {α β } {f : α → β} : (fun x => f x) = (f) := rfl
  rfl
}=
v >>= pure
={
/-- `pure` is a right identity of `>>=` -/
by simp
}=
v
-- ANCHOR_END: mSeqRespId
stop equational steps
-- ANCHOR: mSeqRespIdInit
open MonadApplicativeDesugar
example : seq (pure id) (fun () => v) = v := by simp [seq]
example {f : α → β} : (fun x => f x) = f := by rfl
example :=
  calc
  seq (pure id) (fun () => v) = pure id >>= fun g => (fun () => v) () >>= fun y => pure (g y) := by rfl
  _ = pure id >>= fun g => v >>= fun y => pure (g y) := by rfl
  _ = v >>= fun y => pure (id y) := by simp
  _ = v >>= fun y => pure y := by simp only [id_eq, bind_pure]
  _ = v >>= pure := rfl
  _ = v := by simp only [bind_pure]
-- ANCHOR_END: mSeqRespIdInit
end MonadApplicativeProof1

namespace MonadApplicativeProof2
variable {m : Type → Type}
variable [instM : Monad m]
variable [instLM : LawfulMonad m]
variable {α : Type}
variable {β : Type}
variable {γ : Type}
variable {u : m (β → γ)}
variable {v : m (α → β)}
variable {w : m α}

set_option pp.rawOnError true


open MonadApplicativeDesugar
equational steps : m γ {{{ mSeqRespComp }}}
-- ANCHOR: mSeqRespComp
seq (seq (seq (pure (· ∘ ·)) (fun _ => u))
      (fun _ => v))
  (fun _ => w)
={
/-- Definition of `seq` -/
}=
((pure (· ∘ ·) >>= fun f =>
   u >>= fun x =>
   pure (f x)) >>= fun g =>
  v >>= fun y =>
  pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- `pure` is a left identity of `>>=` -/
by simp only [LawfulMonad.pure_bind]
}=
((u >>= fun x =>
   pure (x ∘ ·)) >>= fun g =>
   v >>= fun y =>
  pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- Insertion of parentheses for clarity -/
}=
((u >>= fun x =>
   pure (x ∘ ·)) >>= (fun g =>
   v >>= fun y =>
  pure (g y))) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- Associativity of `>>=` -/
by simp only [LawfulMonad.bind_assoc]
}=
(u >>= fun x =>
  pure (x ∘ ·) >>= fun g =>
 v  >>= fun y => pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- `pure` is a left identity of `>>=` -/
by simp only [LawfulMonad.pure_bind]
}=
(u >>= fun x =>
  v >>= fun y =>
  pure (x ∘ y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- Associativity of `>>=` -/
by simp only [LawfulMonad.bind_assoc]
}=
u >>= fun x =>
v >>= fun y =>
pure (x ∘ y) >>= fun h =>
w >>= fun z =>
pure (h z)
={
/-- `pure` is a left identity of `>>=` -/
by simp [bind_pure_comp]; rfl
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure ((x ∘ y) z)
={
/-- Definition of function composition -/
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure (x (y z))
={
/--
Time to start moving backwards!
`pure` is a left identity of `>>=`
-/
by simp
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure (y z) >>= fun q =>
pure (x q)
={
/-- Associativity of `>>=` -/
by simp
}=
u >>= fun x =>
v >>= fun y =>
 (w >>= fun p =>
  pure (y p)) >>= fun q =>
 pure (x q)
={
/-- Associativity of `>>=` -/
by simp
}=
u >>= fun x =>
 (v >>= fun y =>
  w >>= fun q =>
  pure (y q)) >>= fun z =>
 pure (x z)
={
/-- This includes the definition of `seq` -/
}=
u >>= fun x =>
seq v (fun () => w) >>= fun q =>
pure (x q)
={
/-- This also includes the definition of `seq` -/
}=
seq u (fun () => seq v (fun () => w))
-- ANCHOR_END: mSeqRespComp
stop equational steps

end MonadApplicativeProof2

namespace MonadApplicativeProof3
variable {m : Type → Type}
variable [instM : Monad m]
variable [instLM : LawfulMonad m]
variable {α : Type}
variable {β : Type}
variable {f : α → β}
variable {x : α}

open MonadApplicativeDesugar
equational steps : m β {{{ mSeqPureNoOp }}}
-- ANCHOR: mSeqPureNoOp
seq (pure f) (fun () => pure x)
={
/-- Replacing `seq` with its definition -/
}=
pure f >>= fun g =>
pure x >>= fun y =>
pure (g y)
={
/-- `pure` is a left identity of `>>=` -/
by simp
}=
pure f >>= fun g =>
pure (g x)
={
/-- `pure` is a left identity of `>>=` -/
by simp
}=
pure (f x)
-- ANCHOR_END: mSeqPureNoOp
stop equational steps
end MonadApplicativeProof3

namespace MonadApplicativeProof4
variable {m : Type → Type}
variable [instM : Monad m]
variable [instLM : LawfulMonad m]
variable {α : Type}
variable {β : Type}
variable {u : m (α → β)}
variable {x : α}

open MonadApplicativeDesugar
equational steps : m β {{{ mSeqPureNoOrder }}}
-- ANCHOR: mSeqPureNoOrder
seq u (fun () => pure x)
={
/-- Definition of `seq` -/
}=
u >>= fun f =>
pure x >>= fun y =>
pure (f y)
={
/-- `pure` is a left identity of `>>=` -/
by simp
}=
u >>= fun f =>
pure (f x)
={
/-- Clever replacement of one expression by an equivalent one that makes the rule match -/
}=
u >>= fun f =>
pure ((fun g => g x) f)
={
/-- `pure` is a left identity of `>>=` -/
by simp [LawfulMonad.pure_bind]
}=
pure (fun g => g x) >>= fun h =>
u >>= fun f =>
pure (h f)
={
/-- Definition of `seq` -/
}=
seq (pure (fun f => f x)) (fun () => u)
-- ANCHOR_END: mSeqPureNoOrder
stop equational steps

end MonadApplicativeProof4

namespace FakeMonad


-- ANCHOR: MonadExtends
class Monad (m : Type → Type) extends Applicative m where
  bind : m α → (α → m β) → m β
  seq f x :=
    bind f fun g =>
    bind (x ()) fun y =>
    pure (g y)
-- ANCHOR_END: MonadExtends

end FakeMonad

theorem NonEmptyList.append_assoc (xs ys zs : NonEmptyList α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  cases xs with
  | mk x xs =>
    cases ys with
    | mk y ys =>
      cases zs with
      | mk x xs =>
        simp only [HAppend.hAppend]
        dsimp [Append.append]
        simp


-- ANCHOR: Validate
inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
-- ANCHOR_END: Validate


-- ANCHOR: FunctorValidate
instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs
-- ANCHOR_END: FunctorValidate


-- ANCHOR: ApplicativeValidate
instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')
-- ANCHOR_END: ApplicativeValidate

instance : LawfulApplicative (Validate ε) where
  map_pure g x := by
    simp [pure, Functor.map]
  map_const {α β} := by
    simp [Functor.mapConst, Functor.map]
  id_map x := by
    simp [Functor.map]
    split <;> rfl
  comp_map g h x := by
    simp [Function.comp, Functor.map]
    split <;> rfl
  seqLeft_eq x y := by
    simp [SeqLeft.seqLeft, Functor.map]
    cases x <;> cases y <;> simp [Seq.seq, Functor.map]
  seqRight_eq x y := by
    cases x <;> cases y <;> simp [SeqRight.seqRight, Functor.map, Seq.seq]
  pure_seq g x := by
    simp [Functor.map, Seq.seq]
  seq_pure g x := by
    cases g <;> simp [Seq.seq, Functor.map]
  seq_assoc x y z := by
    cases x <;> cases y <;> cases z <;> simp [Seq.seq, Functor.map, NonEmptyList.append_assoc]

instance : Monad (Validate ε) where
  bind
    | .errors errs, _ => .errors errs
    | .ok x, f => f x

theorem v_bind_pure (x : Validate ε α) : x >>= pure = x := by
  cases x <;> simp [bind, pure]



/--
error: unsolved goals
case errors.errors
ε α✝ β✝ : Type
a✝¹ a✝ : NonEmptyList ε
⊢ a✝¹ = a✝¹ ++ a✝
-/
#check_msgs in
-- ANCHOR: unlawful
instance : LawfulMonad (Validate ε) where
  bind_pure_comp f x := by
    cases x <;> simp [Functor.map, bind, pure]
  bind_map f x := by
    cases f <;> cases x <;>
    simp [Functor.map, bind, Seq.seq]
  pure_bind x f := by
    simp [bind]
  bind_assoc x f g := by
    cases x <;>
    simp [bind]
-- ANCHOR_END: unlawful

-- ANCHOR: ValidateAndThen
def Validate.andThen (val : Validate ε α)
    (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x
-- ANCHOR_END: ValidateAndThen



-- ANCHOR: RawInput
structure RawInput where
  name : String
  birthYear : String
-- ANCHOR_END: RawInput

namespace SubtypeDemo
-- ANCHOR: Subtype
structure Subtype {α : Type} (p : α → Prop) where
  val : α
  property : p val
-- ANCHOR_END: Subtype

variable {α : Type}
variable {p : α → Prop}

-- ANCHOR: subtypeSugarIn
example := Subtype p
-- ANCHOR_END: subtypeSugarIn

example := GetElem


-- ANCHOR: subtypeSugar
example : (
_root_.Subtype p
) = (
{x : α // p x}
) := rfl
-- ANCHOR_END: subtypeSugar

-- ANCHOR: subtypeSugar2
example : (
_root_.Subtype p
) = (
{x // p x}
) := rfl
-- ANCHOR_END: subtypeSugar2

end SubtypeDemo


namespace FastPos
-- ANCHOR: FastPos
def FastPos : Type := {x : Nat // x > 0}
-- ANCHOR_END: FastPos


-- ANCHOR: one
def one : FastPos := ⟨1, by decide⟩
-- ANCHOR_END: one

-- ANCHOR: onep
example := 1 > 0
-- ANCHOR_END: onep


section
variable {n : Nat}
-- ANCHOR: OfNatFastPos
instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp⟩
-- ANCHOR_END: OfNatFastPos

-- ANCHOR: OfNatFastPosp
example := n + 1 > 0
-- ANCHOR_END: OfNatFastPosp
end

def seven : FastPos := 7

-- ANCHOR: NatFastPosRemarks
section
variable {α} (p : α → Prop)
example := {x : α // p x}
end
-- ANCHOR_END: NatFastPosRemarks

-- ANCHOR: NatFastPos
def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none
-- ANCHOR_END: NatFastPos


end FastPos

-- ANCHOR: CheckedInput
structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
-- ANCHOR_END: CheckedInput

-- ANCHOR: CheckedInputEx
example := CheckedInput 2019
example := CheckedInput 2020
example := (String.toNat? : String → Option Nat)
example := String.trim
-- ANCHOR_END: CheckedInputEx

-- ANCHOR: Field
def Field := String
-- ANCHOR_END: Field


-- ANCHOR: reportError
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }
-- ANCHOR_END: reportError

-- ANCHOR: checkName
def checkName (name : String) :
    Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩
-- ANCHOR_END: checkName


-- ANCHOR: checkYearIsNat
def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n
-- ANCHOR_END: checkYearIsNat

-- ANCHOR: checkBirthYear
def checkBirthYear (thisYear year : Nat) :
    Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"
-- ANCHOR_END: checkBirthYear


-- ANCHOR: checkInput
def checkInput (year : Nat) (input : RawInput) :
    Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat
-- ANCHOR_END: checkInput

deriving instance Repr for NonEmptyList
deriving instance Repr for Validate
deriving instance Repr for CheckedInput


/-- info:
Validate.ok { name := "David", birthYear := 1984 }
-/
#check_msgs in
-- ANCHOR: checkDavid1984
#eval checkInput 2023 {name := "David", birthYear := "1984"}
-- ANCHOR_END: checkDavid1984


/-- info:
Validate.errors { head := ("name", "Required"), tail := [("birth year", "Must be no later than 2023")] }
-/
#check_msgs in
-- ANCHOR: checkBlank2045
#eval checkInput 2023 {name := "", birthYear := "2045"}
-- ANCHOR_END: checkBlank2045

/-- info:
Validate.errors { head := ("birth year", "Must be digits"), tail := [] }
-/
#check_msgs in
-- ANCHOR: checkDavidSyzygy
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}
-- ANCHOR_END: checkDavidSyzygy

namespace SeqCounterexample


-- ANCHOR: counterexample
def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }

def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }
-- ANCHOR_END: counterexample

evaluation steps : Validate String String {{{ realSeq }}}
-- ANCHOR: realSeq
notFun <*> notArg
===>
match notFun with
| .ok g => g <$> notArg
| .errors errs =>
  match notArg with
  | .ok _ => .errors errs
  | .errors errs' => .errors (errs ++ errs')
===>
match notArg with
| .ok _ =>
  .errors { head := "First error", tail := [] }
| .errors errs' =>
  .errors ({ head := "First error", tail := [] } ++ errs')
===>
.errors
  ({ head := "First error", tail := [] } ++
   { head := "Second error", tail := []})
===>
.errors {
  head := "First error",
  tail := ["Second error"]
}
-- ANCHOR_END: realSeq
end evaluation steps



open MonadApplicative in
evaluation steps : Validate String String {{{ fakeSeq }}}
-- ANCHOR: fakeSeq
seq notFun (fun () => notArg)
===>
notFun.andThen fun g =>
notArg.andThen fun y =>
pure (g y)
===>
match notFun with
| .errors errs => .errors errs
| .ok val =>
  (fun g =>
    notArg.andThen fun y =>
    pure (g y)) val
===>
.errors { head := "First error", tail := [] }
-- ANCHOR_END: fakeSeq
end evaluation steps


end SeqCounterexample


-- ANCHOR: LegacyCheckedInput
abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr
-- ANCHOR_END: LegacyCheckedInput

-- ANCHOR: names1
example := @LegacyCheckedInput.company
-- ANCHOR_END: names1

-- ANCHOR: ValidateorElse
def Validate.orElse
    (a : Validate ε α)
    (b : Unit → Validate ε α) :
    Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)
-- ANCHOR_END: ValidateorElse

namespace FakeOrElse


-- ANCHOR: OrElse
class OrElse (α : Type) where
  orElse : α → (Unit → α) → α
-- ANCHOR_END: OrElse
end FakeOrElse

namespace SugaryOrElse

variable {α : Type}
variable [inst : OrElse α]
variable {E1 : α}
variable {E2 : α}

-- ANCHOR: OrElseSugar
example : (
E1 <|> E2
) = (
OrElse.orElse E1 (fun () => E2)
) := rfl
-- ANCHOR_END: OrElseSugar


end SugaryOrElse

-- ANCHOR: OrElseValidate
instance : OrElse (Validate ε α) where
  orElse := Validate.orElse
-- ANCHOR_END: OrElseValidate


-- ANCHOR: checkThat
def checkThat (condition : Bool)
    (field : Field) (msg : String) :
    Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg
-- ANCHOR_END: checkThat


namespace Provisional

-- ANCHOR: checkCompanyProv
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM")
      "birth year" "FIRM if a company" <*>
    checkName input.name
-- ANCHOR_END: checkCompanyProv

end Provisional

namespace SeqRightSugar

variable {f : Type → Type} {α β : Type} [SeqRight f] {E1 : f α} {E2 : f β}

-- ANCHOR: seqRightSugar
example : (
E1 *> E2
) = (
SeqRight.seqRight E1 (fun () => E2)
) := rfl
-- ANCHOR_END: seqRightSugar

-- ANCHOR: seqRightType
example : f α → (Unit → f β) → f β := SeqRight.seqRight
-- ANCHOR_END: seqRightType

end SeqRightSugar

namespace FakeSeqRight


-- ANCHOR: ClassSeqRight
class SeqRight (f : Type → Type) where
  seqRight : f α → (Unit → f β) → f β
-- ANCHOR_END: ClassSeqRight

end FakeSeqRight

namespace Provisional2

-- ANCHOR: checkCompanyProv2
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM")
    "birth year" "FIRM if a company" *>
  pure .company <*> checkName input.name
-- ANCHOR_END: checkCompanyProv2

end Provisional2


-- ANCHOR: checkCompany
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM")
    "birth year" "FIRM if a company" *>
  .company <$> checkName input.name
-- ANCHOR_END: checkCompany


-- ANCHOR: checkSubtype
def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)]
    (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }
-- ANCHOR_END: checkSubtype


-- ANCHOR: checkHumanAfter1970
def checkHumanAfter1970 (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970)
        ("birth year", "greater than 1970") <*>
      checkName input.name
-- ANCHOR_END: checkHumanAfter1970


-- ANCHOR: checkHumanBefore1970
def checkHumanBefore1970 (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970)
        ("birth year", "less than 1970") <*>
      pure input.name
-- ANCHOR_END: checkHumanBefore1970


-- ANCHOR: checkLegacyInput
def checkLegacyInput (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|>
  checkHumanBefore1970 input <|>
  checkHumanAfter1970 input
-- ANCHOR_END: checkLegacyInput


/-- info:
Validate.ok (LegacyCheckedInput.company "Johnny's Troll Groomers")
-/
#check_msgs in
-- ANCHOR: trollGroomers
#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
-- ANCHOR_END: trollGroomers

/-- info:
Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "Johnny")
-/
#check_msgs in
-- ANCHOR: johnny
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
-- ANCHOR_END: johnny

/-- info:
Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "")
-/
#check_msgs in
-- ANCHOR: johnnyAnon
#eval checkLegacyInput ⟨"", "1963"⟩
-- ANCHOR_END: johnnyAnon


/-- info:
Validate.errors
  { head := ("birth year", "FIRM if a company"),
    tail := [("name", "Required"),
             ("birth year", "less than 1970"),
             ("birth year", "greater than 1970"),
             ("name", "Required")] }
-/
#check_msgs in
-- ANCHOR: allFailures
#eval checkLegacyInput ⟨"", "1970"⟩
-- ANCHOR_END: allFailures

-- ANCHOR: TreeError
inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both
-- ANCHOR_END: TreeError


namespace FakeAlternative



-- ANCHOR: FakeAlternative
class Alternative (f : Type → Type) extends Applicative f where
  failure : f α
  orElse : f α → (Unit → f α) → f α
-- ANCHOR_END: FakeAlternative


-- ANCHOR: AltOrElse
instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse
-- ANCHOR_END: AltOrElse
end FakeAlternative


-- ANCHOR: AlternativeOption
instance : Alternative Option where
  failure := none
  orElse
    | some x, _ => some x
    | none, y => y ()
-- ANCHOR_END: AlternativeOption

-- ANCHOR: AlternativeMany
def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

instance : Alternative Many where
  failure := .none
  orElse := Many.orElse
-- ANCHOR_END: AlternativeMany

namespace Guard


-- ANCHOR: guard
def guard [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then
    pure ()
  else failure
-- ANCHOR_END: guard


-- ANCHOR: evenDivisors
def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k
-- ANCHOR_END: evenDivisors


/-- info:
[20, 10, 4, 2]
-/
#check_msgs in
-- ANCHOR: evenDivisors20
#eval (evenDivisors 20).takeAll
-- ANCHOR_END: evenDivisors20

end Guard

-- ANCHOR: FunctorNames
section
example := Functor
example := @Functor.map
example := @Functor.mapConst
open Functor
example := @map
end
-- ANCHOR_END: FunctorNames

-- ANCHOR: ApplicativeNames
section
example := Applicative
end
-- ANCHOR_END: ApplicativeNames


-- ANCHOR: ApplicativeLaws
section
example := Functor
example := Monad
variable {α β γ : Type u} {F : Type u → Type v} [Applicative F] {v : F α} {u : F (β → γ)} {w : F α}
example := pure id <*> v = v
variable {γ : Type u} {v : F (α → β)}
example := pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)
variable (x : α) (f : α → β)
example := @Eq (F β) (pure f <*> pure x) (pure (f x))
variable (u : F (α → β))
example := u <*> pure x = pure (fun f => f x) <*> u
end

section
variable (f : α → β) [Applicative F] (E : F α)
example := pure f <*> E = f <$> E
example := @Functor.map
end
-- ANCHOR_END: ApplicativeLaws

-- ANCHOR: misc
section
example := @Validate.errors
def Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α
  | .ok v, _ => .ok v
  | .errors ⟨x, xs⟩, f => .errors ⟨f x, xs.map f⟩
def report : TreeError → String
  | _ => "TODO (exercise)"
variable {α ε}
example := [Add α, HAdd α α α]
example := Append ε
end
-- ANCHOR_END: misc

-- ANCHOR: ApplicativeOptionLaws1
section
variable {v : Option α}
example : some id <*> v = v := by simp [Seq.seq]
example : id <$> v = v := by simp
-- ANCHOR_END: ApplicativeOptionLaws1
-- ANCHOR: ApplicativeOptionLaws2
variable {α β γ : Type _} {w : Option α} {v : Option (α → β)} {u : Option (β → γ)}
example : some (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w) := by
  simp [Seq.seq, Option.map]
  cases u <;> cases v <;> cases w <;> simp
end
-- ANCHOR_END: ApplicativeOptionLaws2
