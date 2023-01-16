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
  Option α✝ : Type ?u.28
but is expected to have type
  α✝ : Type ?u.28"
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
      | none => y ⟨⟩
stop book declaration



book declaration {{{ getSomeInput }}}
  def getSomeInput : OptionT IO String := do
    let input ← (← IO.getStdin).getLine
    let trimmed := (input.dropWhile (·.isWhitespace)).dropRightWhile (·.isWhitespace)
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
  max ?u.12321 ?u.12322 =?= u
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
        | .notANumber s => pure "Not a number: \"{s}\""
stop book declaration
end Verbose

book declaration {{{ divFrontendSugary }}}
  def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
    try
      pure (toString (← divBackend (← asNumber n) (← asNumber k)))
    catch
      | .divByZero => pure "Division by zero!"
      | .notANumber s => pure "Not a number: \"{s}\""
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

instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (v, s') ← result s
    next v s'



end St
