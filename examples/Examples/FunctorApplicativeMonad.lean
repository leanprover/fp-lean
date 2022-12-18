import Examples.Support
import Examples.Classes
import Examples.Monads.Class


book declaration {{{ MythicalCreature }}}
  structure MythicalCreature where
    large : Bool
stop book declaration


book declaration {{{ Monster }}}
  structure Monster extends MythicalCreature where
    vulnerability : String
stop book declaration


expect info {{{ MythicalCreatureMk }}}
  #check MythicalCreature.mk
message
"MythicalCreature.mk : Bool → MythicalCreature"
end expect

expect info {{{ MythicalCreatureLarge }}}
  #check MythicalCreature.large
message
"MythicalCreature.large : MythicalCreature → Bool"
end expect


expect info {{{ MonsterMk }}}
  #check Monster.mk
message
"Monster.mk : MythicalCreature → String → Monster"
end expect

bookExample type {{{ MonsterToCreature }}}
  Monster.toMythicalCreature
  ===>
  Monster → MythicalCreature
end bookExample


book declaration {{{ Helper }}}
 structure Helper extends MythicalCreature where
    assistance : String
    payment : String
stop book declaration


book declaration {{{ troll }}}
  def troll : Monster where
    large := true
    vulnerability := "sunlight"
stop book declaration

#eval troll.large

namespace Blurble
book declaration {{{ troll2 }}}
  def troll : Monster := {large := true, vulnerability := "sunlight"}
stop book declaration
end Blurble


namespace Foo
expect error {{{ wrongTroll1 }}}
  def troll : Monster := ⟨true, "sunlight"⟩
message
"application type mismatch
  Monster.mk true
argument
  true
has type
  Bool : Type
but is expected to have type
  MythicalCreature : Type"
end expect


book declaration {{{ troll3 }}}
  def troll : Monster := ⟨⟨true⟩, "sunlight"⟩
stop book declaration
end Foo


expect error {{{ trollLargeNoDot }}}
  #eval MythicalCreature.large troll
message
"application type mismatch
  troll.large
argument
  troll
has type
  Monster : Type
but is expected to have type
  MythicalCreature : Type"
end expect

structure Aaa where
  a : Bool

structure Bbb where
  a : Bool
  b : String

structure Ccc extends Aaa, Bbb where


#check Monster.toMythicalCreature


book declaration {{{ elf }}}
  def nisse : Helper where
    large := false
    assistance := "household tasks"
    payment := "porridge"
stop book declaration


book declaration {{{ SizedCreature }}}
  inductive Size where
    | small
    | medium
    | large
  deriving BEq

  structure SizedCreature extends MythicalCreature where
    size : Size
    large := size == Size.large
stop book declaration

book declaration {{{ nonsenseCreature }}}
  def nonsenseCreature : SizedCreature where
    large := false
    size := .large
stop book declaration


book declaration {{{ sizesMatch }}}
  def SizesMatch (sc : SizedCreature) : Prop :=
    sc.large == (sc.size == Size.large)
stop book declaration


book declaration {{{ huldresize }}}
  def huldre : SizedCreature where
    size := .medium

  example : SizesMatch huldre := by
    simp [SizesMatch]
stop book declaration

book declaration {{{ small }}}
  def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
stop book declaration

bookExample {{{ smallTroll }}}
  troll.small
  ===>
  false
end bookExample


expect error {{{ smallTrollWrong }}}
  MythicalCreature.small troll
message
"application type mismatch
  MythicalCreature.small troll
argument
  troll
has type
  Monster : Type
but is expected to have type
  MythicalCreature : Type"
end expect

#eval nisse.small


expect error {{{ smallElfNoDot }}}
  #eval MythicalCreature.small nisse
message
"application type mismatch
  MythicalCreature.small nisse
argument
  nisse
has type
  Helper : Type
but is expected to have type
  MythicalCreature : Type"
end expect

namespace VariousTypes

axiom f : Type → Type
axiom m : Type → Type
@[instance] axiom instF : Applicative f
@[instance] axiom instM : Monad m
axiom α : Type
axiom β : Type

bookExample type {{{ pureType }}}
  pure
  <===
  {α : Type} → α → f α
end bookExample

bookExample type {{{ seqType }}}
  Seq.seq
  <===
  f (α → β) → (Unit → f α) → f β
end bookExample

bookExample type {{{ bindType }}}
  Bind.bind
  <===
  m α → (α → m β) → m β
end bookExample


end VariousTypes

namespace OwnInstances

book declaration {{{ ApplicativeOption }}}
  instance : Applicative Option where
    pure x := .some x
    seq f x :=
      match f with
      | none => none
      | some g => g <$> x ⟨⟩
stop book declaration

book declaration {{{ ApplicativeExcept }}}
  instance : Applicative (Except ε) where
    pure x := .ok x
    seq f x :=
      match f with
      | .error e => .error e
      | .ok g => g <$> x ⟨⟩
stop book declaration

book declaration {{{ ApplicativeReader }}}
  instance : Applicative (Reader ρ) where
    pure x := fun _ => x
    seq f x :=
      fun env =>
        f env (x ⟨⟩ env)
stop book declaration

book declaration {{{ ApplicativeId }}}
  instance : Applicative Id where
    pure x := x
    seq f x := f (x ⟨⟩)
stop book declaration

end OwnInstances

bookExample type {{{ somePlus }}}
  some Plus.plus
  <===
  Option (Nat → Nat → Nat)
end bookExample

bookExample type {{{ somePlusFour }}}
  some Plus.plus <*> some 4
  <===
  Option (Nat → Nat)
end bookExample

bookExample type {{{ somePlusFourSeven }}}
  some Plus.plus <*> some 4 <*> some 7
  <===
  Option Nat
end bookExample



structure NotApplicative (α : Type) where
  impossible : Empty

instance : Functor NotApplicative where
  map _ x := ⟨x.impossible⟩

instance : LawfulFunctor NotApplicative where
  id_map x := nomatch x.impossible
  map_const := by
    simp [Functor.map, Functor.mapConst]
  comp_map g h x := nomatch x.impossible



book declaration {{{ Pair }}}
  structure Pair (α β : Type) : Type where
    first : α
    second : β
stop book declaration

bookExample type {{{ PairType }}}
  Pair
  ===>
  Type → Type → Type
end bookExample


book declaration {{{ FunctorPair }}}
  instance : Functor (Pair α) where
    map f x := ⟨x.first, f x.second⟩
stop book declaration

namespace CheckFunctorPair
axiom α : Type
axiom β : Type
axiom γ : Type
axiom δ : Type
axiom x : α
axiom y : β
axiom f : γ → δ
axiom g : β → γ

evaluation steps {{{ checkPairMapId }}}
  id <$> Pair.mk x y
  ===>
  Pair.mk x (id y)
  ===>
  Pair.mk x y
end evaluation steps

evaluation steps {{{ checkPairMapComp1 }}}
  f <$> g <$> Pair.mk x y
  ===>
  f <$> Pair.mk x (g y)
  ===>
  Pair.mk x (f (g y))
end evaluation steps

evaluation steps {{{ checkPairMapComp2 }}}
  (f ∘ g) <$> Pair.mk x y
  ===>
  Pair.mk x ((f ∘ g) y)
  ===>
  Pair.mk x (f (g y))
end evaluation steps


end CheckFunctorPair

instance : LawfulFunctor (Pair α) where
  id_map x := by
    simp [Functor.map]
  map_const := by
    simp [Function.const, Function.comp, Functor.mapConst, Functor.map]
  comp_map g h x := by
    cases x
    simp [Function.comp, Functor.map]


expect error {{{ Pairpure }}}
  def Pair.pure (x : β) : Pair α β := _
message
"don't know how to synthesize placeholder
context:
β α : Type
x : β
⊢ Pair α β"
end expect



expect error {{{ Pairpure2 }}}
  def Pair.pure (x : β) : Pair α β := Pair.mk _ x
message
"don't know how to synthesize placeholder for argument 'first'
context:
β α : Type
x : β
⊢ α"
end expect

namespace ApplicativeOptionLaws

axiom α : Type
axiom β : Type
axiom γ : Type
axiom δ : Type

axiom x : α
axiom g : α → β
axiom f : β → γ

evaluation steps {{{ OptionHomomorphism1 }}}
  some (· ∘ ·) <*> some f <*> some g <*> some x
  ===>
  some (f ∘ ·) <*> some g <*> some x
  ===>
  some (f ∘ g) <*> some x
  ===>
  some ((f ∘ g) x)
  ===>
  some (f (g x))
end evaluation steps

evaluation steps {{{ OptionHomomorphism2 }}}
  some f <*> (some g <*> some x)
  ===>
  some f <*> (some (g x))
  ===>
  some (f (g x))
end evaluation steps


end ApplicativeOptionLaws

namespace ApplicativeOptionLaws2

axiom α : Type
axiom β : Type

axiom x : α
axiom y : α
axiom f : α → β

evaluation steps {{{ OptionPureSeq }}}
  some f <*> some x
  ===>
  f <$> some x
  ===>
  some (f x)
end evaluation steps


end ApplicativeOptionLaws2


namespace ApplicativeToFunctor

book declaration {{{ ApplicativeMap }}}
  def map [Applicative f] (g : α → β) (x : f α) : f β :=
    pure g <*> x
stop book declaration



book declaration {{{ ApplicativeExtendsFunctorOne }}}
  class Applicative (f : Type → Type) extends Functor f where
    pure : α → f α
    seq : f (α → β) → (Unit → f α) → f β
    map g x := seq (pure g) (fun ⟨⟩ => x)
stop book declaration

end ApplicativeToFunctor

namespace MonadApplicative


book declaration {{{ MonadSeq }}}
  def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
    let g ← f
    let y ← x ⟨⟩
    pure (g y)
stop book declaration

end MonadApplicative

namespace MonadApplicativeDesugar
book declaration {{{ MonadSeqDesugar }}}
  def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
    f >>= fun g =>
    x ⟨⟩ >>= fun y =>
    pure (g y)
stop book declaration

end MonadApplicativeDesugar

equational steps {{{ testEq }}}
  1 + 1
  ={
  -- Foo of `plus` and `stuff`
  }=
  2
stop equational steps

namespace MonadApplicativeProof1
axiom m : Type → Type
@[instance] axiom instM : Monad m
@[instance] axiom instLM : LawfulMonad m
axiom α : Type
axiom v : m α

equational steps {{{ mSeqRespId }}}
  pure id >>= fun g => v >>= fun y => pure (g y)
  ={
  by simp [LawfulMonad.pure_bind]
  -- `pure` is a left identity of `>>=`
  }=
  v >>= fun y => pure (id y)
  ={
  -- Reduce the call to `id`
  }=
  v >>= fun y => pure y
  ={
  -- `fun x => f x` is the same as `f`
  }=
  v >>= pure
  ={
  -- `pure` is a right identity of `>>=`
  by simp [LawfulMonad.bind_pure_comp]
  }=
  v
stop equational steps
end MonadApplicativeProof1

namespace MonadApplicativeProof2
axiom m : Type → Type
@[instance] axiom instM : Monad m
@[instance] axiom instLM : LawfulMonad m
axiom α : Type
axiom β : Type
axiom γ : Type
axiom u : m (β → γ)
axiom v : m (α → β)
axiom w : m α

open MonadApplicativeDesugar
equational steps : m γ {{{ mSeqRespComp }}}
  seq (seq (seq (pure (· ∘ ·)) (fun _ => u)) (fun _ => v)) (fun _ => w)
  ={
  -- Definition of `seq`
  }=
  ((pure (· ∘ ·) >>= fun f =>
     u >>= fun x =>
     pure (f x)) >>= fun g =>
    v >>= fun y =>
    pure (g y)) >>= fun h =>
   w >>= fun z =>
   pure (h z)
  ={
  by simp [LawfulMonad.pure_bind]
  -- `pure` is a left identity of `>>=`
  }=
  ((u >>= fun x =>
     pure (x ∘ ·)) >>= fun g =>
     v >>= fun y =>
    pure (g y)) >>= fun h =>
   w >>= fun z =>
   pure (h z)
  ={
  -- Insertion of parentheses for clarity
  }=
  ((u >>= fun x =>
     pure (x ∘ ·)) >>= (fun g =>
     v >>= fun y =>
    pure (g y))) >>= fun h =>
   w >>= fun z =>
   pure (h z)
  ={
  by simp [LawfulMonad.bind_assoc]
  -- Associativity of `>>=`
  }=
  (u >>= fun x =>
    pure (x ∘ ·) >>= fun g =>
   v  >>= fun y => pure (g y)) >>= fun h =>
   w >>= fun z =>
   pure (h z)
  ={
  by simp [LawfulMonad.pure_bind]
  -- `pure` is a left identity of `>>=`
  }=
  (u >>= fun x =>
    v >>= fun y =>
    pure (x ∘ y)) >>= fun h =>
   w >>= fun z =>
   pure (h z)
  ={
  by simp [LawfulMonad.bind_assoc]
  -- Associativity of `>>=`
  }=
  u >>= fun x =>
  v >>= fun y =>
  pure (x ∘ y) >>= fun h =>
  w >>= fun z =>
  pure (h z)
  ={
  by simp [LawfulMonad.pure_bind]
  -- `pure` is a left identity of `>>=`
  }=
  u >>= fun x =>
  v >>= fun y =>
  w >>= fun z =>
  pure ((x ∘ y) z)
  ={
  -- Definition of function composition
  }=
  u >>= fun x =>
  v >>= fun y =>
  w >>= fun z =>
  pure (x (y z))
  ={
  -- Time to start moving backwards!
  -- `pure` is a left identity of `>>=`
    by simp [LawfulMonad.pure_bind]
  }=
  u >>= fun x =>
  v >>= fun y =>
  w >>= fun z =>
  pure (y z) >>= fun q =>
  pure (x q)
  ={
  by simp [LawfulMonad.bind_assoc]
  -- Associativity of `>>=`
  }=
  u >>= fun x =>
  v >>= fun y =>
   (w >>= fun p =>
    pure (y p)) >>= fun q =>
   pure (x q)
  ={
  by simp [LawfulMonad.bind_assoc]
  -- Associativity of `>>=`
  }=
  u >>= fun x =>
   (v >>= fun y =>
    w >>= fun q =>
    pure (y q)) >>= fun z =>
   pure (x z)
  ={
  -- This includes the definition of `seq`
  }=
  u >>= fun x =>
  seq v (fun ⟨⟩ => w) >>= fun q =>
  pure (x q)
  ={
  -- This also includes the definition of `seq`
  }=
  seq u (fun ⟨⟩ => seq v (fun ⟨⟩ => w))
stop equational steps

end MonadApplicativeProof2

namespace MonadApplicativeProof3
axiom m : Type → Type
@[instance] axiom instM : Monad m
@[instance] axiom instLM : LawfulMonad m
axiom α : Type
axiom β : Type
axiom f : α → β
axiom x : α

open MonadApplicativeDesugar
equational steps : m β {{{ mSeqPureNoOp }}}
  seq (pure f) (fun ⟨⟩ => pure x)
  ={
  -- Replacing `seq` with its definition
  }=
  pure f >>= fun g =>
  pure x >>= fun y =>
  pure (g y)
  ={
  -- `pure` is a left identity of `>>=`
  by simp [LawfulMonad.pure_bind]
  }=
  pure f >>= fun g =>
  pure (g x)
  ={
  -- `pure` is a left identity of `>>=`
  by simp [LawfulMonad.pure_bind]
  }=
  pure (f x)
stop equational steps
end MonadApplicativeProof3

namespace MonadApplicativeProof4
axiom m : Type → Type
@[instance] axiom instM : Monad m
@[instance] axiom instLM : LawfulMonad m
axiom α : Type
axiom β : Type
axiom u : m (α → β)
axiom x : α

open MonadApplicativeDesugar
equational steps : m β {{{ mSeqPureNoOrder }}}
  seq u (fun ⟨⟩ => pure x)
  ={
  -- Definition of `seq`
  }=
  u >>= fun f =>
  pure x >>= fun y =>
  pure (f y)
  ={
  -- `pure` is a left identity of `>>=`
  by simp [LawfulMonad.pure_bind]
  }=
  u >>= fun f =>
  pure (f x)
  ={
  -- Clever replacement of one expression by an equivalent one that makes the rule match
  }=
  u >>= fun f =>
  pure ((fun g => g x) f)
  ={
  -- `pure` is a left identity of `>>=`
  by simp [LawfulMonad.pure_bind]
  }=
  pure (fun g => g x) >>= fun h =>
  u >>= fun f =>
  pure (h f)
  ={
  -- Definition of `seq`
  }=
  seq (pure (fun f => f x)) (fun ⟨⟩ => u)
stop equational steps

end MonadApplicativeProof4

namespace FakeMonad


book declaration {{{ MonadExtends }}}
  class Monad (m : Type → Type) extends Applicative m where
    bind : m α → (α → m β) → m β
    seq f x :=
      bind f fun g =>
      bind (x ⟨⟩) fun y =>
      pure (g y)
stop book declaration

end FakeMonad

theorem NonEmptyList.append_assoc (xs ys zs : NonEmptyList α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  cases xs with
  | mk x xs =>
    cases ys with
    | mk y ys =>
      cases zs with
      | mk x xs =>
        simp [HAppend.hAppend, Append.append]
        apply List.append_assoc

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α

instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => Functor.map g (x ⟨⟩)
    | .errors errs =>
      match x ⟨⟩ with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

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
    simp [SeqLeft.seqLeft, Function.const, Functor.map]
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



expect error {{{ unlawful }}}
  instance : LawfulMonad (Validate ε) where
    bind_pure_comp f x := by
      cases x <;> simp [Functor.map, bind, pure]
    bind_map f x := by
      cases f <;> cases x <;>
      simp [Functor.map, bind, Seq.seq]
    pure_bind x f := by
      simp [bind, pure]
    bind_assoc x f g := by
      cases x <;>
      simp [bind]
message
"unsolved goals
case errors.errors
ε α✝ β✝ : Type
a✝¹ a✝ : NonEmptyList ε
⊢ a✝¹ = a✝¹ ++ a✝"
end expect

def Validate.andThen (val1 : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val1 with
  | .errors errs => .errors errs
  | .ok x => next x

structure RawInput where
  name : String
  birthYear : String

structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}

def Field := String

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = ""
    then .errors ⟨("name", "Required"), []⟩
    else .ok ⟨name, by assumption⟩

def double_negation (notNot : ¬¬p) : p := by
  by_cases p
  case inl => assumption
  case inr => contradiction

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  let noWS := (year.dropWhile Char.isWhitespace).dropRightWhile Char.isWhitespace
  match noWS.toNat? with
  | none => .errors ⟨("birth year", "Must be digits"), []⟩
  | .some n => pure n

def checkBirthYear (thisYear year : Nat) : Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : ¬(year > 1900)
    then .errors ⟨("birth year", "Must be after 1900"), []⟩
    else if h' : ¬(year ≤ thisYear)
      then .errors ⟨("birth year", s!"Must be no later than {thisYear}"), []⟩
      else .ok ⟨year, by constructor <;> simp [double_negation, *]⟩


def check (year : Nat) (input : RawInput) : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen (checkBirthYear year)

deriving instance Repr for NonEmptyList
deriving instance Repr for Validate
deriving instance Repr for CheckedInput

#eval check 2022 {name := "David", birthYear := "1984"}
#eval check 2022 {name := "", birthYear := "2045"}
#eval check 2022 {name := "David", birthYear := "nineteen eighty four"}

