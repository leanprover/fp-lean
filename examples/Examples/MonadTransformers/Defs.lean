import Examples.Support

namespace Opt


book declaration {{{ OptionTdef }}}
  def OptionT (m : Type u → Type v) (α : Type u) : Type v :=
    m (Option α)
stop book declaration

expect error {{{ firstMonadOptionT }}}
  instance [Monad m] : Monad (OptionT m) where
    pure x := pure (some x)
    bind action next := do
      match (← action) with
      | none => pure none
      | some v => next v
message
"application type mismatch
  pure (some x)
argument
  some x
has type
  Option α✝ : Type ?u.25
but is expected to have type
  α✝ : Type ?u.25"
end expect

namespace OneAttempt

book declaration {{{ MonadOptionTAnnots }}}
  instance [Monad m] : Monad (OptionT m) where
    pure x := (pure (some x) : m (Option _))
    bind action next := (do
      match (← action) with
      | none => pure none
      | some v => next v : m (Option _))
stop book declaration

end OneAttempt

namespace Structed

book declaration {{{ OptionTStructure }}}
  structure OptionT (m : Type u → Type v) (α : Type u) : Type v where
    run : m (Option α)
stop book declaration


end Structed


book declaration {{{ FakeStructOptionT }}}
def OptionT.mk (x : m (Option α)) : OptionT m α := x

def OptionT.run (x : OptionT m α) : m (Option α) := x
stop book declaration


book declaration {{{ MonadOptionTFakeStruct }}}
  instance [Monad m] : Monad (OptionT m) where
    pure x := OptionT.mk (pure (some x))
    bind action next := OptionT.mk do
      match ← action with
      | none => pure none
      | some v => next v
stop book declaration

namespace Lawful

axiom α : Type
axiom β : Type
axiom γ : Type
axiom m : Type → Type
axiom v : α
axiom w : m (Option α)
axiom f : α → OptionT m β
axiom g : β → OptionT m γ
@[instance] axiom inst0 : Monad m
@[instance] axiom inst1 : LawfulMonad m

equational steps {{{ OptionTFirstLaw }}}
  bind (pure v) f
  ={ by simp [bind, pure, OptionT.mk]
  -- Unfolding the definitions of `bind` and `pure`
  }=
  OptionT.mk do
    match ← pure (some v) with
    | none => pure none
    | some x => f x
  ={
  -- Desugaring nested action syntax
  }=
  OptionT.mk do
    let y ← pure (some v)
    match y with
    | none => pure none
    | some x => f x
  ={
  -- Desugaring `do`-notation
  }=
  OptionT.mk
    (pure (some v) >>= fun y =>
      match y with
      | none => pure none
      | some x => f x)
  ={
    -- Using the first monad rule for `m`
    by simp [LawfulMonad.pure_bind]
  }=
  OptionT.mk
    (match some v with
     | none => pure none
     | some x => f x)
  ={
  -- Reduce `match`
  }=
  OptionT.mk (f v)
  ={
  -- Definition of `OptionT.mk`
  }=
  f v
stop equational steps

end Lawful


book declaration {{{ LiftOptionT }}}
  instance [Monad m] : MonadLift m (OptionT m) where
    monadLift action := OptionT.mk do
      pure (some (← action))
stop book declaration


book declaration {{{ AlternativeOptionT }}}
  instance [Monad m] : Alternative (OptionT m) where
    failure := OptionT.mk (pure none)
    orElse x y := OptionT.mk do
      match ← x with
      | some result => pure (some result)
      | none => y ()
stop book declaration



book declaration {{{ getSomeInput }}}
  def getSomeInput : OptionT IO String := do
    let input ← (← IO.getStdin).getLine
    let trimmed := input.trim
    if trimmed == "" then
      failure
    else pure trimmed
stop book declaration


book declaration {{{ UserInfo }}}
  structure UserInfo where
    name : String
    favoriteBeetle : String
stop book declaration


book declaration {{{ getUserInfo }}}
  def getUserInfo : OptionT IO UserInfo := do
    IO.println "What is your name?"
    let name ← getSomeInput
    IO.println "What is your favorite species of beetle?"
    let beetle ← getSomeInput
    pure ⟨name, beetle⟩
stop book declaration


book declaration {{{ interact }}}
  def interact : IO Unit := do
    match ← getUserInfo with
    | none => IO.eprintln "Missing info"
    | some ⟨name, beetle⟩ => IO.println s!"Hello {name}, whose favorite beetle is {beetle}."
stop book declaration

end Opt



namespace Ex


book declaration {{{ ExceptT }}}
  def ExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
    m (Except ε α)
stop book declaration

namespace Huh

book declaration {{{ ExceptTNoUnis }}}
  def ExceptT.mk (x : m (Except ε α)) : ExceptT ε m α := x
stop book declaration

expect error {{{ MonadMissingUni }}}
  instance {ε : Type u} {m : Type u → Type v} [Monad m] : Monad (ExceptT ε m) where
    pure x := ExceptT.mk (pure (Except.ok x))
    bind result next := ExceptT.mk do
      match (← result) with
      | .error e => pure (.error e)
      | .ok x => next x
message
"stuck at solving universe constraint
  max ?u.12144 ?u.12145 =?= u
while trying to unify
  ExceptT ε m α✝
with
  (ExceptT ε m α✝) ε m α✝"
end expect
end Huh

book declaration {{{ ExceptTFakeStruct }}}
  def ExceptT.mk {ε α : Type u} (x : m (Except ε α)) : ExceptT ε m α := x

  def ExceptT.run {ε α : Type u} (x : ExceptT ε m α) : m (Except ε α) := x
stop book declaration

book declaration {{{ MonadExceptT }}}
  instance {ε : Type u} {m : Type u → Type v} [Monad m] : Monad (ExceptT ε m) where
    pure x := ExceptT.mk (pure (Except.ok x))
    bind result next := ExceptT.mk do
      match ← result with
      | .error e => pure (.error e)
      | .ok x => next x
stop book declaration


book declaration {{{ ExceptTLiftExcept }}}
  instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
    monadLift action := ExceptT.mk (pure action)
stop book declaration


book declaration {{{ ExceptTLiftM }}}
  instance [Monad m] : MonadLift m (ExceptT ε m) where
    monadLift action := ExceptT.mk (.ok <$> action)
stop book declaration

namespace MyMonadExcept
book declaration {{{ MonadExcept }}}
  class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
    throw : ε → m α
    tryCatch : m α → (ε → m α) → m α
stop book declaration
end MyMonadExcept


book declaration {{{ ErrEx }}}
  inductive Err where
    | divByZero
    | notANumber : String → Err
stop book declaration


book declaration {{{ divBackend }}}
  def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
    if k == 0 then
      throw .divByZero
    else pure (n / k)
stop book declaration


book declaration {{{ asNumber }}}
  def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
    match s.toInt? with
    | none => throw (.notANumber s)
    | some i => pure i
stop book declaration

namespace Verbose
book declaration {{{ divFrontend }}}
  def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
    tryCatch (do pure (toString (← divBackend (← asNumber n) (← asNumber k))))
      fun
        | .divByZero => pure "Division by zero!"
        | .notANumber s => pure s!"Not a number: \"{s}\""
stop book declaration
end Verbose

book declaration {{{ divFrontendSugary }}}
  def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
    try
      pure (toString (← divBackend (← asNumber n) (← asNumber k)))
    catch
      | .divByZero => pure "Division by zero!"
      | .notANumber s => pure s!"Not a number: \"{s}\""
stop book declaration

example : @Verbose.divFrontend = @divFrontend := by rfl


bookExample type {{{ OptionExcept }}}
  inferInstance
  <===
  MonadExcept Unit Option
end bookExample


end Ex

namespace St


book declaration {{{ DefStateT }}}
  def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
    σ → m (α × σ)
stop book declaration


book declaration {{{ MonadStateT }}}
  instance [Monad m] : Monad (StateT σ m) where
    pure x := fun s => pure (x, s)
    bind result next := fun s => do
      let (v, s') ← result s
      next v s'
stop book declaration

instance [Monad m] : MonadStateOf σ (StateT σ m) where
  get := fun s => pure (s, s)
  set s' := fun _ => pure ((), s')
  modifyGet f := fun s => pure (f s)


end St


namespace StEx


book declaration {{{ countLetters }}}
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
stop book declaration

namespace Modify

book declaration {{{ countLettersModify }}}
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
stop book declaration

book declaration {{{ modify }}}
  def modify [MonadState σ m] (f : σ → σ) : m Unit :=
    modifyGet fun s => ((), f s)
stop book declaration

end Modify

namespace Reorder

book declaration {{{ countLettersClassy }}}
  def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept Err m] (str : String) : m Unit :=
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
stop book declaration


book declaration {{{ SomeMonads }}}
  abbrev M1 := StateT LetterCounts (ExceptT Err Id)
  abbrev M2 := ExceptT Err (StateT LetterCounts Id)
stop book declaration


expect info {{{ countLettersM1Ok }}}
  #eval countLetters (m := M1) "hello" ⟨0, 0⟩
message
"Except.ok ((), { vowels := 2, consonants := 3 })"
end expect


expect info {{{ countLettersM2Ok }}}
  #eval countLetters (m := M2) "hello" ⟨0, 0⟩
message
"(Except.ok (), { vowels := 2, consonants := 3 })"
end expect


expect info {{{ countLettersM1Error }}}
  #eval countLetters (m := M1) "hello!" ⟨0, 0⟩
message
"Except.error (StEx.Err.notALetter '!')"
end expect

expect info {{{ countLettersM2Error }}}
  #eval countLetters (m := M2) "hello!" ⟨0, 0⟩
message
"(Except.error (StEx.Err.notALetter '!'), { vowels := 2, consonants := 3 })"
end expect




book declaration {{{ countWithFallback }}}
  def countWithFallback
      [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
      (str : String) : m Unit :=
    try
      countLetters str
    catch _ =>
      countLetters "Fallback"
stop book declaration


expect info {{{ countWithFallbackM1Ok }}}
  #eval countWithFallback (m := M1) "hello" ⟨0, 0⟩
message
"Except.ok ((), { vowels := 2, consonants := 3 })"
end expect


expect info {{{ countWithFallbackM2Ok }}}
  #eval countWithFallback (m := M2) "hello" ⟨0, 0⟩
message
"(Except.ok (), { vowels := 2, consonants := 3 })"
end expect


expect info {{{ countWithFallbackM1Error }}}
  #eval countWithFallback (m := M1) "hello!" ⟨0, 0⟩
message
"Except.ok ((), { vowels := 2, consonants := 6 })"
end expect


expect info {{{ countWithFallbackM2Error }}}
  #eval countWithFallback (m := M2) "hello!" ⟨0, 0⟩
message
"(Except.ok (), { vowels := 4, consonants := 9 })"
end expect

axiom α : Type
axiom σ : Type
axiom σ' : Type

bookExample {{{ M1eval }}}
  M1 α
  ===>
  LetterCounts → Except Err (α × LetterCounts)
end bookExample

bookExample {{{ M2eval }}}
  M2 α
  ===>
  LetterCounts → Except Err α × LetterCounts
end bookExample


bookExample {{{ StateTDoubleA }}}
  StateT σ (StateT σ' Id) α
  ===>
  σ → σ' → ((α × σ) × σ')
end bookExample

bookExample {{{ StateTDoubleB }}}
  StateT σ' (StateT σ Id) α
  ===>
  σ' → σ → ((α × σ') × σ)
end bookExample


end Reorder

namespace Cls


book declaration {{{ MonadState }}}
  class MonadState (σ : outParam (Type u)) (m : Type u → Type v) : Type (max (u+1) v) where
    get : m σ
    set : σ → m PUnit
    modifyGet : (σ → α × σ) → m α
stop book declaration

end Cls


universe u
universe v
bookExample type {{{ getTheType }}}
  getThe
  ===>
  (σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → m σ
end bookExample

bookExample type {{{ modifyTheType }}}
  modifyThe
  ===>
  (σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → (σ → σ) → m PUnit
end bookExample



end StEx

similar datatypes MonadState StEx.Cls.MonadState
