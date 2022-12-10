import Examples.Support
import Examples.Classes


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


book declaration {{{ fitsInDoor }}}
  def fitsInDoor (creature : MythicalCreature) : Bool :=
    !creature.large
stop book declaration

expect error {{{ fitsInDoorElf }}}
  fitsInDoor nisse
message
"application type mismatch
  fitsInDoor nisse
argument
  nisse
has type
  Helper : Type
but is expected to have type
  MythicalCreature : Type"
end expect


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


#eval fitsInDoor nisse.toMythicalCreature
#eval fitsInDoor troll.toMythicalCreature

structure NotApplicative (α : Type) where
  impossible : Empty

instance : Functor NotApplicative where
  map _ x := ⟨x.impossible⟩

instance : LawfulFunctor NotApplicative where
  id_map x := nomatch x.impossible
  map_const := by
    simp [Functor.map, Functor.mapConst]
  comp_map g h x := nomatch x.impossible


structure Pair (α β : Type) : Type where
  first : α
  second : β

instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩

instance : LawfulFunctor (Pair α) where
  id_map x := by
    simp [Functor.map]
  map_const := by
    simp [Function.const, Function.comp, Functor.mapConst, Functor.map]
  comp_map g h x := by
    cases x
    simp [Function.comp, Functor.map]

def Pair.pure (x : β) : Pair α β := _

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
