import Examples.Support

namespace FinDef

book declaration {{{ Fin }}}
  structure Fin (n : Nat) where
    val  : Nat
    isLt : LT.lt val n
stop book declaration



end FinDef

expect info {{{ fiveFinEight }}}
  #eval (5 : Fin 8)
message
"5"
end expect


expect info {{{ finOverflow }}}
  #eval (45 : Fin 10)
message
"5"
end expect

def Fin.next? (i : Fin n) : Option (Fin n) :=
  if h : i.val + 1 < n then
    some ⟨i.val + 1, h⟩
  else
    none


expect info {{{ nextThreeFin }}}
  #eval (3 : Fin 8).next?
message
"some 4"
end expect


expect info {{{ nextSevenFin }}}
  #eval (7 : Fin 8).next?
message
"none"
end expect



namespace Finny

book declaration {{{ ArrayFindHelper }}}
  -- TODO check text for new termination_by syntax
  def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Fin arr.size × α) :=
    if h : i < arr.size then
      let x := arr[i]
      if p x then
        some (⟨i, h⟩, x)
      else findHelper arr p (i + 1)
    else none
  termination_by arr.size - i
stop book declaration

book declaration {{{ ArrayFind }}}
  def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
    findHelper arr p 0
stop book declaration


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
