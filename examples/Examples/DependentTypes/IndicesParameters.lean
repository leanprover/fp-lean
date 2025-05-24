import ExampleSupport
import Examples.DependentTypes

-- ANCHOR: WithParameter
inductive WithParameter (α : Type u) : Type u where
  | test : α → WithParameter α
-- ANCHOR_END: WithParameter


-- ANCHOR: WithTwoParameters
inductive WithTwoParameters (α : Type u) (β : Type v) : Type (max u v) where
  | test : α → β → WithTwoParameters α β
-- ANCHOR_END: WithTwoParameters


-- ANCHOR: WithParameterAfterColon
inductive WithParameterAfterColon : Type u → Type u where
  | test : α → WithParameterAfterColon α
-- ANCHOR_END: WithParameterAfterColon


-- ANCHOR: WithParameterAfterColon2
inductive WithParameterAfterColon2 : Type u → Type u where
  | test1 : α → WithParameterAfterColon2 α
  | test2 : WithParameterAfterColon2 α
-- ANCHOR_END: WithParameterAfterColon2



-- ANCHOR: WithParameterAfterColonDifferentNames
inductive WithParameterAfterColonDifferentNames : Type u → Type u where
  | test1 : α → WithParameterAfterColonDifferentNames α
  | test2 : β → WithParameterAfterColonDifferentNames β
-- ANCHOR_END: WithParameterAfterColonDifferentNames


/-- error:
inductive datatype parameter mismatch
  β
expected
  α
-/
#check_msgs in
-- ANCHOR: WithParameterBeforeColonDifferentNames
inductive WithParameterBeforeColonDifferentNames (α : Type u) : Type u where
  | test1 : α → WithParameterBeforeColonDifferentNames α
  | test2 : β → WithParameterBeforeColonDifferentNames β
-- ANCHOR_END: WithParameterBeforeColonDifferentNames

/-- error:
inductive datatype parameter mismatch
  α × α
expected
  α
-/
#check_msgs in
-- ANCHOR: WithNamedIndex
inductive WithNamedIndex (α : Type u) : Type (u + 1) where
  | test1 : WithNamedIndex α
  | test2 : WithNamedIndex α → WithNamedIndex α → WithNamedIndex (α × α)
-- ANCHOR_END: WithNamedIndex


-- ANCHOR: WithIndex
inductive WithIndex : Type u → Type (u + 1) where
  | test1 : WithIndex α
  | test2 : WithIndex α → WithIndex α → WithIndex (α × α)
-- ANCHOR_END: WithIndex

/-- error:
invalid universe level in constructor 'ParamAfterIndex.test1', parameter 'γ' has type
  Type u
at universe level
  u+2
which is not less than or equal to the inductive type's resulting universe level
  u+1
-/
#check_msgs in
-- ANCHOR: ParamAfterIndex
inductive ParamAfterIndex : Nat → Type u → Type u where
  | test1 : ParamAfterIndex 0 γ
  | test2 : ParamAfterIndex n γ → ParamAfterIndex k γ → ParamAfterIndex (n + k) γ
-- ANCHOR_END: ParamAfterIndex


/-- error:
inductive datatype parameter mismatch
  4
expected
  n
-/
#check_msgs in
-- ANCHOR: NatParamFour
inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam 4 5
-- ANCHOR_END: NatParamFour


-- ANCHOR: NatParam
inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam n 5
-- ANCHOR_END: NatParam


/-- info:
inductive Vect.{u} : Type u → Nat → Type u
number of parameters: 1
constructors:
Vect.nil : {α : Type u} → Vect α 0
Vect.cons : {α : Type u} → {n : Nat} → α → Vect α n → Vect α (n + 1)
-/
#check_msgs in
-- ANCHOR: printVect
#print Vect
-- ANCHOR_END: printVect
