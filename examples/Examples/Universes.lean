import ExampleSupport


/-- info:
Prop : Type
-/
#check_msgs in
-- ANCHOR: PropType
#check Prop
-- ANCHOR_END: PropType


/-- info:
Type : Type 1
-/
#check_msgs in
-- ANCHOR: TypeType
#check Type
-- ANCHOR_END: TypeType

/-- info:
Type : Type 1
-/
#check_msgs in
-- ANCHOR: Type0Type
#check Type 0
-- ANCHOR_END: Type0Type


#check List Type

-- ANCHOR: Type1Type
example : Type 2 := Type 1
-- ANCHOR_END: Type1Type

-- ANCHOR: Type2Type
example : Type 3 := Type 2
-- ANCHOR_END: Type2Type

-- ANCHOR: Type3Type
example : Type 4 := Type 3
-- ANCHOR_END: Type3Type

-- ANCHOR: NatNatType
example : Type := Nat → Nat
-- ANCHOR_END: NatNatType


-- ANCHOR: Fun00Type
example : Type 1 := Type → Type
-- ANCHOR_END: Fun00Type


-- ANCHOR: Fun12Type
example : Type 3 := Type 1 → Type 2
-- ANCHOR_END: Fun12Type

-- ANCHOR: FunPropType
example : Prop := (n : Nat) → n = n + 0
-- ANCHOR_END: FunPropType

-- ANCHOR: FunTypePropType
example : Prop := Type → 2 + 2 = 4
-- ANCHOR_END: FunTypePropType

namespace MyList1


-- ANCHOR: MyList1
inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
-- ANCHOR_END: MyList1

-- ANCHOR: MyList1Type
example : Type → Type := MyList
-- ANCHOR_END: MyList1Type


/-- error:
application type mismatch
  MyList Type
argument
  Type
has type
  Type 1 : Type 2
but is expected to have type
  Type : Type 1
-/
#check_msgs in
-- ANCHOR: myListNat1Err
def myListOfNat : MyList Type :=
  .cons Nat .nil
-- ANCHOR_END: myListNat1Err

end MyList1

namespace MyList15


-- ANCHOR: MyList15
inductive MyList (α : Type 1) : Type 1 where
  | nil : MyList α
  | cons : α → MyList α → MyList α
-- ANCHOR_END: MyList15

-- ANCHOR: MyList15Type
example : Type 1 → Type 1 := MyList
-- ANCHOR_END: MyList15Type


-- ANCHOR: myListOfNat15
def myListOfNat : MyList Type :=
  .cons Nat .nil
-- ANCHOR_END: myListOfNat15
end MyList15




/-- error:
invalid universe level in constructor 'MyList.cons', parameter has type
  α
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
-/
#check_msgs in
-- ANCHOR: MyList2
inductive MyList (α : Type 1) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
-- ANCHOR_END: MyList2


namespace MyList3


-- ANCHOR: MyList3
inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α
-- ANCHOR_END: MyList3

-- ANCHOR: myListOfNat3
def myListOfNumbers : MyList Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList Type :=
  .cons Nat .nil
-- ANCHOR_END: myListOfNat3

-- ANCHOR: myListOfList3
def myListOfList : MyList (Type → Type) :=
  .cons MyList .nil
-- ANCHOR_END: myListOfList3

namespace Explicit

-- ANCHOR: MyListDotZero
example : Type → Type := MyList.{0}
-- ANCHOR_END: MyListDotZero
-- ANCHOR: MyListDotOne
example : Type 1 → Type 1 := MyList.{1}
-- ANCHOR_END: MyListDotOne
-- ANCHOR: MyListDotTwo
example : Type 2 → Type 2 := MyList.{2}
-- ANCHOR_END: MyListDotTwo


-- ANCHOR: myListOfList3Expl
def myListOfNumbers : MyList.{0} Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList.{1} Type :=
  .cons Nat .nil

def myListOfList : MyList.{1} (Type → Type) :=
  .cons MyList.{0} .nil
-- ANCHOR_END: myListOfList3Expl

end Explicit

end MyList3


namespace MySum


namespace Inflexible


-- ANCHOR: SumNoMax
inductive Sum (α : Type u) (β : Type u) : Type u where
  | inl : α → Sum α β
  | inr : β → Sum α β
-- ANCHOR_END: SumNoMax


-- ANCHOR: SumPoly
def stringOrNat : Sum String Nat := .inl "hello"

def typeOrType : Sum Type Type := .inr Nat
-- ANCHOR_END: SumPoly

/-- error:
application type mismatch
  Sum String Type
argument
  Type
has type
  Type 1 : Type 2
but is expected to have type
  Type : Type 1
-/
#check_msgs in
-- ANCHOR: stringOrTypeLevels
def stringOrType : Sum String Type := .inr Nat
-- ANCHOR_END: stringOrTypeLevels

end Inflexible


-- ANCHOR: SumMax
inductive Sum (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
-- ANCHOR_END: SumMax


-- ANCHOR: stringOrTypeSum
def stringOrType : Sum String Type := .inr Nat
-- ANCHOR_END: stringOrTypeSum

end MySum

namespace PropStuff


-- ANCHOR: someTrueProps
def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
-- ANCHOR_END: someTrueProps

namespace Explicit

-- ANCHOR: someTruePropsExp
def someTruePropositions : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
-- ANCHOR_END: someTruePropsExp

end Explicit

-- ANCHOR: ArrProp
example : Prop := (n : Nat) → n + 0 = n
-- ANCHOR_END: ArrProp


end PropStuff
