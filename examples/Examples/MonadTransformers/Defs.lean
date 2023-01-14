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


end Ex
