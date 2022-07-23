import Examples.Support

class Plus (α : Type) where
  plus : α → α → α

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
  deriving Repr

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus


def double [Plus α] (x : α) (y : α) : α := Plus.plus x y

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
