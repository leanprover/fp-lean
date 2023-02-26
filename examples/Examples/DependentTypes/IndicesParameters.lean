import Examples.Support


book declaration {{{ WithParameter }}}
  inductive WithParameter (α : Type u) : Type u where
    | test : α → WithParameter α
stop book declaration


book declaration {{{ WithTwoParameters }}}
  inductive WithTwoParameters (α : Type u) (β : Type v) : Type (max u v) where
    | test : α → WithTwoParameters α β
stop book declaration


book declaration {{{ WithParameterAfterColon }}}
  inductive WithParameterAfterColon : Type u → Type u where
    | test : α → WithParameterAfterColon α
stop book declaration


book declaration {{{ WithParameterAfterColon2 }}}
  inductive WithParameterAfterColon2 : Type u → Type u where
    | test1 : α → WithParameterAfterColon2 α
    | test2 : WithParameterAfterColon2 α
stop book declaration

inductive WithParameterAfterColon3 : Type u → Type u where
  | test1 : WithParameterAfterColon α
  | test2 : WithParameterAfterColon β

inductive WithNamedIndex (α : Type u) : Type (u + 1) where
  | test1 : WithNamedIndex α
  | test2 : WithNamedIndex α → WithNamedIndex β → WithNamedIndex (α × β)


inductive WithIndex : Type u → Type u where
  | test1 : WithIndex α
  | test2 : WithIndex α → WithIndex β → WithIndex (α × β)

inductive WithIndex : Nat → Type u → Type u where
  | test1 : WithIndex 0 γ
  | test2 : WithIndex n γ → WithIndex k γ → WithIndex (n + k) γ
