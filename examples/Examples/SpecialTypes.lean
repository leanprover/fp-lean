-- ANCHOR: all
example := List
example := [UInt8, UInt16, UInt32, UInt64, USize, Int8, Int16, Int32, Int64, ISize]
example := Fin (2 ^ 32)
example := [Nat, List Unit, String, Int, Char, List Char]
example {w} := BitVec w
example := [true, false]
example {x : α} := [some x, none]
example := ∀ {n k : Nat}, n ≠ 0 → k ≠ 0 → n + k ≠ 0
example := [Add, Mul, ToString]
example := Nat.succ
section
universe u
example := Sort u
end
-- ANCHOR_END: all

-- ANCHOR: sequences
section
example {α} := [List α, Array α]
open Array
example : Array α → List α := toList
end
-- ANCHOR_END: sequences

-- ANCHOR: StringDetail
section
open String
example : String → List Char := data
end
-- ANCHOR_END: StringDetail
