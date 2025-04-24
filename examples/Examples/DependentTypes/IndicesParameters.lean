import Examples.Support
import Examples.DependentTypes

book declaration {{{ WithParameter }}}
  inductive WithParameter (α : Type u) : Type u where
    | test : α → WithParameter α
stop book declaration


book declaration {{{ WithTwoParameters }}}
  inductive WithTwoParameters (α : Type u) (β : Type v) : Type (max u v) where
    | test : α → β → WithTwoParameters α β
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



book declaration {{{ WithParameterAfterColonDifferentNames }}}
  inductive WithParameterAfterColonDifferentNames : Type u → Type u where
    | test1 : α → WithParameterAfterColonDifferentNames α
    | test2 : β → WithParameterAfterColonDifferentNames β
stop book declaration


expect error {{{ WithParameterBeforeColonDifferentNames }}}
  inductive WithParameterBeforeColonDifferentNames (α : Type u) : Type u where
    | test1 : α → WithParameterBeforeColonDifferentNames α
    | test2 : β → WithParameterBeforeColonDifferentNames β
message
"inductive datatype parameter mismatch
  β
expected
  α"
end expect

expect error {{{ WithNamedIndex }}}
  inductive WithNamedIndex (α : Type u) : Type (u + 1) where
    | test1 : WithNamedIndex α
    | test2 : WithNamedIndex α → WithNamedIndex α → WithNamedIndex (α × α)
message
"inductive datatype parameter mismatch
  α × α
expected
  α"
end expect


book declaration {{{ WithIndex }}}
  inductive WithIndex : Type u → Type (u + 1) where
    | test1 : WithIndex α
    | test2 : WithIndex α → WithIndex α → WithIndex (α × α)
stop book declaration

expect error {{{ ParamAfterIndex }}}
  inductive ParamAfterIndex : Nat → Type u → Type u where
    | test1 : ParamAfterIndex 0 γ
    | test2 : ParamAfterIndex n γ → ParamAfterIndex k γ → ParamAfterIndex (n + k) γ
message
"invalid universe level in constructor 'ParamAfterIndex.test1', parameter 'γ' has type
  Type u
at universe level
  u+2
which is not less than or equal to the inductive type's resulting universe level
  u+1"
end expect


expect error {{{ NatParamFour }}}
  inductive NatParam (n : Nat) : Nat → Type u where
    | five : NatParam 4 5
message
"inductive datatype parameter mismatch
  4
expected
  n"
end expect


book declaration {{{ NatParam }}}
  inductive NatParam (n : Nat) : Nat → Type u where
    | five : NatParam n 5
stop book declaration


expect info {{{ printVect }}}
  #print Vect
message
"inductive Vect.{u} : Type u → Nat → Type u
number of parameters: 1
constructors:
Vect.nil : {α : Type u} → Vect α 0
Vect.cons : {α : Type u} → {n : Nat} → α → Vect α n → Vect α (n + 1)"
end expect
