import ExampleSupport

set_option linter.unusedVariables false

-- ANCHOR: various
example := Functor
example := @Functor.map
example := Monad
example := @HAdd.hAdd
example := semiOutParam
example := Id
-- ANCHOR_END: various

namespace Opt


-- ANCHOR: OptionTdef
def OptionT (m : Type u → Type v) (α : Type u) : Type v :=
  m (Option α)
-- ANCHOR_END: OptionTdef

/--
error: Application type mismatch: The argument
  some x
has type
  Option α✝
but is expected to have type
  α✝
in the application
  pure (some x)
---
error: failed to synthesize
  Pure (OptionT m)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: Type mismatch
  none
has type
  Option ?m.24
but is expected to have type
  α✝
---
error: failed to synthesize
  Bind (OptionT m)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: firstMonadOptionT
instance [Monad m] : Monad (OptionT m) where
  pure x := pure (some x)
  bind action next := do
    match (← action) with
    | none => pure none
    | some v => next v
-- ANCHOR_END: firstMonadOptionT

namespace OneAttempt

-- ANCHOR: MonadOptionTAnnots
instance [Monad m] : Monad (OptionT m) where
  pure x := (pure (some x) : m (Option _))
  bind action next := (do
    match (← action) with
    | none => pure none
    | some v => next v : m (Option _))
-- ANCHOR_END: MonadOptionTAnnots

end OneAttempt

namespace Structed

-- ANCHOR: OptionTStructure
structure OptionT (m : Type u → Type v) (α : Type u) : Type v where
  run : m (Option α)
-- ANCHOR_END: OptionTStructure

-- ANCHOR: OptionTStructuredefs
example := @OptionT.mk
example := @OptionT.run
-- ANCHOR_END: OptionTStructuredefs

end Structed


-- ANCHOR: FakeStructOptionT
def OptionT.mk (x : m (Option α)) : OptionT m α := x

def OptionT.run (x : OptionT m α) : m (Option α) := x
-- ANCHOR_END: FakeStructOptionT


-- ANCHOR: MonadOptionTFakeStruct
instance [Monad m] : Monad (OptionT m) where
  pure x := OptionT.mk (pure (some x))
  bind action next := OptionT.mk do
    match ← action with
    | none => pure none
    | some v => next v
-- ANCHOR_END: MonadOptionTFakeStruct

namespace Lawful

variable (α : Type)
variable (β : Type)
variable (γ : Type)
variable (m : Type → Type)
variable (v : α)
variable (w : m (Option α))
variable (f : α → OptionT m β)
variable (g : β → OptionT m γ)
variable [Monad m]
variable [LawfulMonad m]

equational steps  {{{ OptionTFirstLaw }}}
-- ANCHOR: OptionTFirstLaw
bind (pure v) f
={ /-- Unfolding the definitions of `bind` and `pure` -/
   by simp [bind, pure, OptionT.mk]
}=
OptionT.mk do
  match ← pure (some v) with
  | none => pure none
  | some x => f x
={
/-- Desugaring nested action syntax -/
}=
OptionT.mk do
  let y ← pure (some v)
  match y with
  | none => pure none
  | some x => f x
={
/-- Desugaring `do`-notation -/
}=
OptionT.mk
  (pure (some v) >>= fun y =>
    match y with
    | none => pure none
    | some x => f x)
={
  /-- Using the first monad rule for `m` -/
  by simp [LawfulMonad.pure_bind (m := m)]
}=
OptionT.mk
  (match some v with
   | none => pure none
   | some x => f x)
={
/-- Reduce `match` -/
}=
OptionT.mk (f v)
={
/-- Definition of `OptionT.mk` -/
}=
f v
-- ANCHOR_END: OptionTFirstLaw
stop equational steps

--ANCHOR: OptionTSecondLaw
example := bind w pure
example :=
OptionT.mk do
    match ← w with
    | none => pure none
    | some v => pure (some v)
example := w >>= fun y => pure y
--ANCHOR_END: OptionTSecondLaw

--ANCHOR: OptionTThirdLaw
example {v} := bind (bind v f) g = bind v (fun x => bind (f x) g)
--ANCHOR_END: OptionTThirdLaw
end Lawful


-- ANCHOR: LiftOptionT
instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk do
    pure (some (← action))
-- ANCHOR_END: LiftOptionT


-- ANCHOR: AlternativeOptionT
instance [Monad m] : Alternative (OptionT m) where
  failure := OptionT.mk (pure none)
  orElse x y := OptionT.mk do
    match ← x with
    | some result => pure (some result)
    | none => y ()
-- ANCHOR_END: AlternativeOptionT



-- ANCHOR: getSomeInput
def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trim
  if trimmed == "" then
    failure
  else pure trimmed
-- ANCHOR_END: getSomeInput


-- ANCHOR: UserInfo
structure UserInfo where
  name : String
  favoriteBeetle : String
-- ANCHOR_END: UserInfo


-- ANCHOR: getUserInfo
def getUserInfo : OptionT IO UserInfo := do
  IO.println "What is your name?"
  let name ← getSomeInput
  IO.println "What is your favorite species of beetle?"
  let beetle ← getSomeInput
  pure ⟨name, beetle⟩
-- ANCHOR_END: getUserInfo


-- ANCHOR: interact
def interact : IO Unit := do
  match ← getUserInfo with
  | none =>
    IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ =>
    IO.println s!"Hello {name}, whose favorite beetle is {beetle}."
-- ANCHOR_END: interact

end Opt



namespace Ex


-- ANCHOR: ExceptT
def ExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)
-- ANCHOR_END: ExceptT

namespace Huh

-- ANCHOR: ExceptTNoUnis
def ExceptT.mk (x : m (Except ε α)) : ExceptT ε m α := x
-- ANCHOR_END: ExceptTNoUnis

/--
error: stuck at solving universe constraint
  max ?u.10268 ?u.10269 =?= u
while trying to unify
  ExceptT ε m α✝ : Type v
with
  ExceptT.{max ?u.10269 ?u.10268, v} ε m α✝ : Type v
---
error: stuck at solving universe constraint
  max ?u.10439 ?u.10440 =?= u
while trying to unify
  ExceptT ε m β✝ : Type v
with
  ExceptT.{max ?u.10440 ?u.10439, v} ε m β✝ : Type v
---
error: stuck at solving universe constraint
  max ?u.10268 ?u.10269 =?= u
while trying to unify
  ExceptT ε m α✝ : Type v
with
  ExceptT.{max ?u.10269 ?u.10268, v} ε m α✝ : Type v
-/
#check_msgs in
-- ANCHOR: MonadMissingUni
instance {ε : Type u} {m : Type u → Type v} [Monad m] :
    Monad (ExceptT ε m) where
  pure x := ExceptT.mk (pure (Except.ok x))
  bind result next := ExceptT.mk do
    match (← result) with
    | .error e => pure (.error e)
    | .ok x => next x
-- ANCHOR_END: MonadMissingUni
end Huh

-- ANCHOR: ExceptTFakeStruct
  def ExceptT.mk {ε α : Type u} (x : m (Except ε α)) : ExceptT ε m α := x

  def ExceptT.run {ε α : Type u} (x : ExceptT ε m α) : m (Except ε α) := x
-- ANCHOR_END: ExceptTFakeStruct

-- ANCHOR: MonadExceptT
instance {ε : Type u} {m : Type u → Type v} [Monad m] :
    Monad (ExceptT ε m) where
  pure x := ExceptT.mk (pure (Except.ok x))
  bind result next := ExceptT.mk do
    match ← result with
    | .error e => pure (.error e)
    | .ok x => next x
-- ANCHOR_END: MonadExceptT


-- ANCHOR: ExceptTLiftExcept
instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift action := ExceptT.mk (pure action)
-- ANCHOR_END: ExceptTLiftExcept


-- ANCHOR: ExceptTLiftM
instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift action := ExceptT.mk (.ok <$> action)
-- ANCHOR_END: ExceptTLiftM

namespace MyMonadExcept
-- ANCHOR: MonadExcept
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
  throw : ε → m α
  tryCatch : m α → (ε → m α) → m α
-- ANCHOR_END: MonadExcept
end MyMonadExcept


-- ANCHOR: ErrEx
inductive Err where
  | divByZero
  | notANumber : String → Err
-- ANCHOR_END: ErrEx


-- ANCHOR: divBackend
def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
  if k == 0 then
    throw .divByZero
  else pure (n / k)
-- ANCHOR_END: divBackend


-- ANCHOR: asNumber
def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
  match s.toInt? with
  | none => throw (.notANumber s)
  | some i => pure i
-- ANCHOR_END: asNumber

namespace Verbose
-- ANCHOR: divFrontend
def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  tryCatch (do pure (toString (← divBackend (← asNumber n) (← asNumber k))))
    fun
      | .divByZero => pure "Division by zero!"
      | .notANumber s => pure s!"Not a number: \"{s}\""
-- ANCHOR_END: divFrontend
end Verbose

-- ANCHOR: divFrontendSugary
def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  try
    pure (toString (← divBackend (← asNumber n) (← asNumber k)))
  catch
    | .divByZero => pure "Division by zero!"
    | .notANumber s => pure s!"Not a number: \"{s}\""
-- ANCHOR_END: divFrontendSugary

example : @Verbose.divFrontend = @divFrontend := by rfl


-- ANCHOR: OptionExcept
example : MonadExcept Unit Option := inferInstance
-- ANCHOR_END: OptionExcept


end Ex

namespace St


-- ANCHOR: DefStateT
def StateT (σ : Type u)
    (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)
-- ANCHOR_END: DefStateT


-- ANCHOR: MonadStateT
instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (v, s') ← result s
    next v s'
-- ANCHOR_END: MonadStateT

instance [Monad m] : MonadStateOf σ (StateT σ m) where
  get := fun s => pure (s, s)
  set s' := fun _ => pure ((), s')
  modifyGet f := fun s => pure (f s)


end St


namespace StEx


-- ANCHOR: countLetters
structure LetterCounts where
  vowels : Nat
  consonants : Nat
deriving Repr

inductive Err where
  | notALetter : Char → Err
deriving Repr

def vowels :=
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper )

def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      let st ← get
      let st' ←
        if c.isAlpha then
          if vowels.contains c then
            pure {st with vowels := st.vowels + 1}
          else if consonants.contains c then
            pure {st with consonants := st.consonants + 1}
          else -- modified or non-English letter
            pure st
        else throw (.notALetter c)
      set st'
      loop cs
  loop str.toList
-- ANCHOR_END: countLetters

namespace Modify

-- ANCHOR: countLettersModify
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList
-- ANCHOR_END: countLettersModify

-- ANCHOR: modify
def modify [MonadState σ m] (f : σ → σ) : m Unit :=
  modifyGet fun s => ((), f s)
-- ANCHOR_END: modify

end Modify

namespace Reorder

-- ANCHOR: countLettersClassy
def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
    (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList
-- ANCHOR_END: countLettersClassy


-- ANCHOR: SomeMonads
abbrev M1 := StateT LetterCounts (ExceptT Err Id)
abbrev M2 := ExceptT Err (StateT LetterCounts Id)
-- ANCHOR_END: SomeMonads

-- ANCHOR: m
example := ReaderT
example := MonadReader
example := Except
example {α} := IO (Option α)
-- ANCHOR_END: m

-- ANCHOR: general
section
variable {T : (Type u → Type v) → Type u → Type v} {m : Type u → Type v} [Monad m] [Monad (T m)]
variable [MonadLift m (T m)]
example {α} := m α → T m α
example {α x} := (monadLift (pure x : m α)) = (pure x : T m α)
example {α x f} := monadLift (x >>= f : m α) = ((monadLift x : m α) >>= fun y => monadLift (f y) : T m α)
end
-- ANCHOR_END: general

/-- info:
Except.ok ((), { vowels := 2, consonants := 3 })
-/
#check_msgs in
-- ANCHOR: countLettersM1Ok
#eval countLetters (m := M1) "hello" ⟨0, 0⟩
-- ANCHOR_END: countLettersM1Ok


/-- info:
(Except.ok (), { vowels := 2, consonants := 3 })
-/
#check_msgs in
-- ANCHOR: countLettersM2Ok
#eval countLetters (m := M2) "hello" ⟨0, 0⟩
-- ANCHOR_END: countLettersM2Ok


/-- info:
Except.error (StEx.Err.notALetter '!')
-/
#check_msgs in
-- ANCHOR: countLettersM1Error
#eval countLetters (m := M1) "hello!" ⟨0, 0⟩
-- ANCHOR_END: countLettersM1Error

/-- info:
(Except.error (StEx.Err.notALetter '!'), { vowels := 2, consonants := 3 })
-/
#check_msgs in
-- ANCHOR: countLettersM2Error
#eval countLetters (m := M2) "hello!" ⟨0, 0⟩
-- ANCHOR_END: countLettersM2Error




-- ANCHOR: countWithFallback
def countWithFallback
    [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
    (str : String) : m Unit :=
  try
    countLetters str
  catch _ =>
    countLetters "Fallback"
-- ANCHOR_END: countWithFallback


/-- info:
Except.ok ((), { vowels := 2, consonants := 3 })
-/
#check_msgs in
-- ANCHOR: countWithFallbackM1Ok
#eval countWithFallback (m := M1) "hello" ⟨0, 0⟩
-- ANCHOR_END: countWithFallbackM1Ok


/-- info:
(Except.ok (), { vowels := 2, consonants := 3 })
-/
#check_msgs in
-- ANCHOR: countWithFallbackM2Ok
#eval countWithFallback (m := M2) "hello" ⟨0, 0⟩
-- ANCHOR_END: countWithFallbackM2Ok


/-- info:
Except.ok ((), { vowels := 2, consonants := 6 })
-/
#check_msgs in
-- ANCHOR: countWithFallbackM1Error
#eval countWithFallback (m := M1) "hello!" ⟨0, 0⟩
-- ANCHOR_END: countWithFallbackM1Error


/-- info:
(Except.ok (), { vowels := 4, consonants := 9 })
-/
#check_msgs in
-- ANCHOR: countWithFallbackM2Error
#eval countWithFallback (m := M2) "hello!" ⟨0, 0⟩
-- ANCHOR_END: countWithFallbackM2Error

variable (α : Type)
variable (σ : Type)
variable (σ' : Type)

-- ANCHOR: M1eval
example : (
M1 α
) = (
LetterCounts → Except Err (α × LetterCounts)
) := rfl
-- ANCHOR_END: M1eval

-- ANCHOR: M2eval
example : (
M2 α
) = (
LetterCounts → Except Err α × LetterCounts
) := rfl
-- ANCHOR_END: M2eval


-- ANCHOR: StateTDoubleA
example : (
StateT σ (StateT σ' Id) α
) = (
σ → σ' → ((α × σ) × σ')
) := rfl
-- ANCHOR_END: StateTDoubleA

-- ANCHOR: StateTDoubleB
example : (
StateT σ' (StateT σ Id) α
) = (
σ' → σ → ((α × σ') × σ)
) := rfl
-- ANCHOR_END: StateTDoubleB


end Reorder

namespace Cls


-- ANCHOR: MonadState
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) :
    Type (max (u+1) v) where
  get : m σ
  set : σ → m PUnit
  modifyGet : (σ → α × σ) → m α
-- ANCHOR_END: MonadState

end Cls

example {σ m : _} [MonadStateOf σ m] : MonadState σ m := inferInstance

universe u
universe v
-- ANCHOR: getTheType
example : (σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → m σ := getThe
-- ANCHOR_END: getTheType

-- ANCHOR: modifyTheType
example :
(σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] →
(σ → σ) → m PUnit
:= modifyThe
-- ANCHOR_END: modifyTheType



end StEx

similar datatypes MonadState StEx.Cls.MonadState
