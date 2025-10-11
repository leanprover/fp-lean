import ExampleSupport
import Examples.Classes

-- ANCHOR: sundries
example := Type
example := Type 3
example := Prop
example := Empty
example := Option
example := Nat → Bool
example := @List.all
example := [true, false]
example {α} := Bool → α
-- ANCHOR_END: sundries

-- ANCHOR: NatOrBool
inductive NatOrBool where
  | nat | bool

abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool
-- ANCHOR_END: NatOrBool

-- ANCHOR: natOrBoolExamples
example := NatOrBool.nat.asType
example := NatOrBool.bool.asType
-- ANCHOR_END: natOrBoolExamples

-- ANCHOR: decode
def decode (t : NatOrBool) (input : String) : Option t.asType :=
  match t with
  | .nat => input.toNat?
  | .bool =>
    match input with
    | "true" => some true
    | "false" => some false
    | _ => none
-- ANCHOR_END: decode


-- ANCHOR: NestedPairs
inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs

abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2
-- ANCHOR_END: NestedPairs



/--
error: failed to synthesize
  BEq t.asType

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: beqNoCases
instance {t : NestedPairs} : BEq t.asType where
  beq x y := x == y
-- ANCHOR_END: beqNoCases

-- ANCHOR: NestedPairsbeq
def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

instance {t : NestedPairs} : BEq t.asType where
  beq x y := t.beq x y
-- ANCHOR_END: NestedPairsbeq





-- ANCHOR: Finite
inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite

abbrev Finite.asType : Finite → Type
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr dom cod => asType dom → asType cod
-- ANCHOR_END: Finite

def Finite.count : Finite → Nat
  | .unit => 1
  | .bool => 2
  | .pair t1 t2 => count t1 * count t2
  | .arr dom cod => count cod ^ count dom


-- ANCHOR: ListProduct
def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse
-- ANCHOR_END: ListProduct

def List.concatMap : List α → (α → List β) → List β
  | [], _ => []
  | x :: xs, f => f x ++ xs.concatMap f

namespace ListExtras

-- ANCHOR: foldr
def List.foldr (f : α → β → β) (default : β) : List α → β
  | []     => default
  | a :: l => f a (foldr f default l)
-- ANCHOR_END: foldr
end ListExtras

evaluation steps  {{{ foldrSum }}}
-- ANCHOR: foldrSum
[1, 2, 3, 4, 5].foldr (· + ·) 0
===>
(1 :: 2 :: 3 :: 4 :: 5 :: []).foldr (· + ·) 0
===>
(1 + 2 + 3 + 4 + 5 + 0)
===>
15
-- ANCHOR_END: foldrSum
end evaluation steps


-- ANCHOR: MutualStart
mutual
  -- ANCHOR: FiniteAll
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
    -- ANCHOR_END: MutualStart
    | .unit => [()]
    | .bool => [true, false]
    | .pair t1 t2 => t1.enumerate.product t2.enumerate
    | .arr dom cod => dom.functions cod.enumerate
  -- ANCHOR_END: FiniteAll

  -- ANCHOR: FiniteFunctions
-- ANCHOR: FiniteFunctionSigStart
def Finite.functions
    (t : Finite)
    (results : List α) : List (t.asType → α) :=
  match t with
  -- ANCHOR_END: FiniteFunctionSigStart
  -- ANCHOR: FiniteFunctionUnit
| .unit =>
  results.map fun r =>
    fun () => r
  -- ANCHOR_END: FiniteFunctionUnit
  -- ANCHOR: FiniteFunctionBool
| .bool =>
  (results.product results).map fun (r1, r2) =>
    fun
      | true => r1
      | false => r2
  -- ANCHOR_END: FiniteFunctionBool
  -- ANCHOR: FiniteFunctionPair
| .pair t1 t2 =>
  let f1s := t1.functions <| t2.functions results
  f1s.map fun f =>
    fun (x, y) =>
      f x y
  -- ANCHOR_END: FiniteFunctionPair
  -- ANCHOR: MutualEnd
-- ANCHOR: FiniteFunctionArr
    | .arr t1 t2 =>
      let args := t1.enumerate
      let base :=
        results.map fun r =>
          fun _ => r
      args.foldr
        (fun arg rest =>
          (t2.functions rest).map fun more =>
            fun f => more (f arg) f)
        base
  -- ANCHOR_END: FiniteFunctions
  -- ANCHOR_END: FiniteFunctionArr
end
  -- ANCHOR_END: MutualEnd


-- ANCHOR: FiniteBeq
def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .unit => true
  | .bool => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr dom cod =>
    dom.enumerate.all fun arg => beq cod (x arg) (y arg)
-- ANCHOR_END: FiniteBeq

theorem list_all_true : List.all xs (fun _ => true) = true := by
  simp

theorem beq_refl (t : Finite) (x : t.asType) : t.beq x x = true := by
  induction t with
  | unit => simp [Finite.beq]
  | bool => cases x <;> simp [Finite.beq]
  | pair t1 t2 ih1 ih2 =>
    simp [Finite.beq, *]
  | arr t1 t2 ih1 ih2 =>
    simp [Finite.beq, *]

def Finite.isSingleton : Finite → Bool
  | .unit => true
  | .bool => false
  | .pair t1 t2 => not (isSingleton t1) || not (isSingleton t2)
  | .arr _ cod => not (isSingleton cod)


def Finite.print : (t : Finite) → (x : t.asType) → String
  | .unit, _ => "()"
  | .bool, b => toString b
  | .pair t1 t2, (x, y) => s!"({print t1 x}, {print t2 y})"
  | .arr dom cod, f =>
    let table := dom.enumerate |>.map fun x => s!"({print dom x} ↦ {print cod (f x)})"
    "{" ++ ", ".separate table ++ "}"


def prop (t : Finite) : (Nat × Nat × Bool) := (t.enumerate.length, t.count, t.enumerate.length == t.count)

#eval prop (.arr .bool .unit)
#eval prop (.arr .bool (.pair .unit .bool))
#eval prop (.arr (.arr .bool (.pair (.arr .bool .unit) .bool)) (.pair .unit .bool))
#eval prop (.arr (.arr (.pair .bool .bool) .bool) .bool)


-- ANCHOR: lots
example : (.arr (.arr (.pair .bool .bool) .bool) .bool : Finite).asType = (((Bool × Bool) → Bool) → Bool) := rfl
-- ANCHOR_END: lots
/-- info:
65536
-/
#check_msgs in
-- ANCHOR: nestedFunLength
#eval Finite.enumerate (.arr (.arr (.pair .bool .bool) .bool) .bool) |>.length
-- ANCHOR_END: nestedFunLength

#eval Finite.enumerate (.arr .bool .unit) |>.map (Finite.print _)
#eval Finite.enumerate (.arr .bool .bool) |>.map (Finite.print _)
#eval Finite.enumerate (.arr (.arr .unit .bool) .bool) |>.map (Finite.print _)


/-- info:
true
-/
#check_msgs in
-- ANCHOR: arrBoolBoolEq
#eval Finite.beq (.arr .bool .bool) (fun _ => true) (fun b => b == b)
-- ANCHOR_END: arrBoolBoolEq


/-- info:
false
-/
#check_msgs in
-- ANCHOR: arrBoolBoolEq2
#eval Finite.beq (.arr .bool .bool) (fun _ => true) not
-- ANCHOR_END: arrBoolBoolEq2


/-- info:
true
-/
#check_msgs in
-- ANCHOR: arrBoolBoolEq3
#eval Finite.beq (.arr .bool .bool) id (not ∘ not)
-- ANCHOR_END: arrBoolBoolEq3
