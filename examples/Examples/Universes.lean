import Examples.Support


expect info {{{ PropType }}}
  #check Prop
message
"Prop : Type"
end expect


expect info {{{ TypeType }}}
  #check Type
message
"Type : Type 1"
end expect

expect info {{{ Type0Type }}}
  #check Type 0
message
"Type : Type 1"
end expect


#check List Type

bookExample type {{{ Type1Type }}}
  Type 1
  ===>
  Type 2
end bookExample

bookExample type {{{ Type2Type }}}
  Type 2
  ===>
  Type 3
end bookExample

bookExample type {{{ Type3Type }}}
  Type 3
  ===>
  Type 4
end bookExample

bookExample type {{{ NatNatType }}}
  Nat → Nat
  ===>
  Type
end bookExample


bookExample type {{{ Fun00Type }}}
  Type → Type
  ===>
  Type 1
end bookExample


bookExample type {{{ Fun12Type }}}
  Type 1 → Type 2
  ===>
  Type 3
end bookExample

namespace MyList1


book declaration {{{ MyList1 }}}
  inductive MyList (α : Type) : Type where
    | nil : MyList α
    | cons : α → MyList α → MyList α
stop book declaration

bookExample type {{{ MyList1Type }}}
  MyList
  ===>
  Type → Type
end bookExample


expect error {{{ myListNat1Err }}}
  def myListOfNat : MyList Type :=
    .cons Nat .nil
message
"application type mismatch
  MyList Type
argument
  Type
has type
  Type 1 : Type 2
but is expected to have type
  Type : Type 1"
end expect

end MyList1

namespace MyList15


book declaration {{{ MyList15 }}}
  inductive MyList (α : Type 1) : Type 1 where
    | nil : MyList α
    | cons : α → MyList α → MyList α
stop book declaration

bookExample type {{{ MyList15Type }}}
  MyList
  ===>
  Type 1 → Type 1
end bookExample


book declaration {{{ myListOfNat15 }}}
  def myListOfNat : MyList Type :=
    .cons Nat .nil
stop book declaration
end MyList15




expect error {{{ MyList2 }}}
  inductive MyList (α : Type 1) : Type where
    | nil : MyList α
    | cons : α → MyList α → MyList α
message
"invalid universe level in constructor 'MyList.cons', parameter has type
  α
at universe level
  2
it must be smaller than or equal to the inductive datatype universe level
  1"
end expect


namespace MyList3


book declaration {{{ MyList3 }}}
  inductive MyList (α : Type u) : Type u where
    | nil : MyList α
    | cons : α → MyList α → MyList α
stop book declaration

book declaration {{{ myListOfNat3 }}}
  def myListOfNumbers : MyList Nat :=
    .cons 0 (.cons 1 .nil)

  def myListOfNat : MyList Type :=
    .cons Nat .nil
stop book declaration

book declaration {{{ myListOfList3 }}}
  def myListOfList : MyList (Type → Type) :=
    .cons MyList .nil
stop book declaration

namespace Explicit

bookExample type {{{ MyListDotZero }}}
  MyList.{0}
  ===>
  Type → Type
end bookExample
bookExample type {{{ MyListDotOne }}}
  MyList.{1}
  ===>
  Type 1 → Type 1
end bookExample
bookExample type {{{ MyListDotTwo }}}
  MyList.{2}
  ===>
  Type 2 → Type 2
end bookExample


book declaration {{{ myListOfList3Expl }}}
  def myListOfNumbers : MyList.{0} Nat :=
    .cons 0 (.cons 1 .nil)

  def myListOfNat : MyList.{1} Type :=
    .cons Nat .nil

  def myListOfList : MyList.{1} (Type → Type) :=
    .cons MyList.{0} .nil
stop book declaration

end Explicit

end MyList3


namespace MySum


namespace Inflexible


book declaration {{{ SumNoMax }}}
  inductive Sum (α : Type u) (β : Type u) : Type u where
    | inl : α → Sum α β
    | inr : β → Sum α β
stop book declaration


book declaration {{{ SumPoly }}}
  def stringOrNat : Sum String Nat := .inl "hello"

  def typeOrType : Sum Type Type := .inr Nat
stop book declaration

expect error {{{ stringOrTypeLevels }}}
  def stringOrType : Sum String Type := .inr Nat
message
"application type mismatch
  Sum String Type
argument
  Type
has type
  Type 1 : Type 2
but is expected to have type
  Type : Type 1"
end expect

end Inflexible


book declaration {{{ SumMax }}}
  inductive Sum (α : Type u) (β : Type v) : Type (max u v) where
    | inl : α → Sum α β
    | inr : β → Sum α β
stop book declaration


book declaration {{{ stringOrTypeSum }}}
  def stringOrType : Sum String Type := .inr Nat
stop book declaration

end MySum

namespace PropStuff


book declaration {{{ someTrueProps }}}
  def someTruePropositions : List Prop := [
    1 + 1 = 2,
    "Hello, " ++ "world!" = "Hello, world!"
  ]
stop book declaration

namespace Explicit

book declaration {{{ someTruePropsExp }}}
  def someTruePropositions : List.{0} Prop := [
    1 + 1 = 2,
    "Hello, " ++ "world!" = "Hello, world!"
  ]
stop book declaration

end Explicit

bookExample type {{{ ArrProp }}}
  (n : Nat) → n + 0 = n
  ===>
  Prop
end bookExample


end PropStuff
