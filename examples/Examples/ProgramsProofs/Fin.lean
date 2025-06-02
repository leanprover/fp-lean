import ExampleSupport

namespace FinDef

-- ANCHOR: Fin
structure Fin (n : Nat) where
  val  : Nat
  isLt : LT.lt val n
-- ANCHOR_END: Fin



end FinDef

--ANCHOR: sundries
example := GetElem
example := Array
example := Nat
example {n} := Fin n
example : List (Fin 3) := [0, 1, 2]
example := Fin 0
example := @Subtype
section
variable {n k : Nat}
#synth ToString (Fin n)
#synth OfNat (Fin (n + 1)) k
end
--ANCHOR_END: sundries

/-- info:
5
-/
#check_msgs in
-- ANCHOR: fiveFinEight
#eval (5 : Fin 8)
-- ANCHOR_END: fiveFinEight


/-- info:
5
-/
#check_msgs in
-- ANCHOR: finOverflow
#eval (45 : Fin 10)
-- ANCHOR_END: finOverflow

-- ANCHOR: exercise
def Fin.next? (i : Fin n) : Option (Fin n) :=
  if h : i.val + 1 < n then
    some ⟨i.val + 1, h⟩
  else
    none

section
variable {n}
#check (Fin.next? : Fin n → Option (Fin n))
end
-- ANCHOR_END: exercise

/-- info:
some 4
-/
#check_msgs in
-- ANCHOR: nextThreeFin
#eval (3 : Fin 8).next?
-- ANCHOR_END: nextThreeFin


/-- info:
none
-/
#check_msgs in
-- ANCHOR: nextSevenFin
#eval (7 : Fin 8).next?
-- ANCHOR_END: nextSevenFin



namespace Finny

-- ANCHOR: ArrayFindHelper
def findHelper (arr : Array α) (p : α → Bool) (i : Nat) :
    Option (Fin arr.size × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (⟨i, h⟩, x)
    else findHelper arr p (i + 1)
  else none
-- ANCHOR_END: ArrayFindHelper

-- ANCHOR: ArrayFind
def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
  findHelper arr p 0
-- ANCHOR_END: ArrayFind


  def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Fin arr.size) : Array β :=
    let nextAccum := soFar.push (f arr[i])
    if h : i.val + 1 < arr.size then
      have : Array.size arr - (i.val + 1) < Array.size arr - i.val := by
        apply Nat.sub_succ_lt_self
        exact i.isLt
      arrayMapHelper f arr nextAccum ⟨i + 1, h⟩
    else
      nextAccum
  termination_by arr.size - i.val


  def Array.map (f : α → β) (arr : Array α) : Array β :=
    if h : arr.size > 0 then
      arrayMapHelper f arr Array.empty ⟨0, h⟩
    else
      Array.empty
end Finny
