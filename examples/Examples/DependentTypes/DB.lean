import Examples.Support

inductive BaseDBType where
  | int | string | bool

abbrev BaseDBType.asType : BaseDBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool

instance {t : BaseDBType} : BEq t.asType := by
  cases t <;> exact inferInstance

instance {t : BaseDBType} : Repr t.asType := by
  cases t <;> exact inferInstance

inductive DBType where
  | base : BaseDBType → DBType
  | nullable : BaseDBType → DBType

instance : Coe BaseDBType DBType where
  coe := .base

abbrev DBType.asType : DBType → Type
  | .base t => t.asType
  | .nullable t => Option t.asType

instance {t : DBType} : BEq t.asType := by
  cases t <;> exact inferInstance

instance {t : DBType} : Repr t.asType := by
  cases t <;> exact inferInstance

structure Column where
  name : String
  contains : DBType

abbrev Schema := List Column

inductive Row : Schema → Type where
  | nil : Row []
  | cons : c.contains.asType → Row cols → Row (c :: cols)

deriving instance Repr for Row

def Row.bEq : (r1 r2 : Row s) → Bool
  | .nil, .nil => true
  | .cons v1 r1, .cons v2 r2 => v1 == v2 && bEq r1 r2

instance : BEq (Row s) where
  beq := Row.bEq

abbrev Table (s : Schema) := List (Row s)

abbrev peak : Schema :=
  [⟨"name", BaseDBType.string⟩, ⟨"location", BaseDBType.string⟩, ⟨"elevation", BaseDBType.int⟩, ⟨"lastVisited", .nullable .int⟩]

def mountainDiary : Table peak := [
  .cons "Mount Nebo"       <| .cons "USA"     <| .cons 3637 <| .cons (some 2013) .nil,
  .cons "Moscow Mountain"  <| .cons "USA"     <| .cons 1519 <| .cons (some 2015) .nil,
  .cons "Himmelbjerget"    <| .cons "Denmark" <| .cons  147 <| .cons none        .nil,
  .cons "Mount St. Helens" <| .cons "USA"     <| .cons 2549 <| .cons none        .nil
]

abbrev waterfall : Schema :=
  [⟨"name", BaseDBType.string⟩, ⟨"location", BaseDBType.string⟩, ⟨"lastVisited", .nullable .int⟩]

def waterfallDiary : Table waterfall := [
  .cons "Multnomah Falls" <| .cons "USA" <| .cons (some 2019) .nil,
  .cons "Shoshone Falls"  <| .cons "USA" <| .cons (some 2014) .nil
]

class inductive Subschema : Schema → Schema → Type where
  | keep : Subschema bigger smaller → Subschema (c :: bigger) (c :: smaller)
  | drop : Subschema bigger smaller → Subschema (c :: bigger) smaller
  | done : Subschema [] []

instance [inst : Subschema bigger smaller] : Subschema (c :: bigger) (c :: smaller) := .keep inst
instance [inst : Subschema bigger smaller] : Subschema (c :: bigger) smaller := .drop inst
instance : Subschema [] [] := .done

abbrev travelDiary : Schema :=
  [⟨"name", BaseDBType.string⟩, ⟨"location", BaseDBType.string⟩, ⟨"lastVisited", .nullable .int⟩]

example : Subschema peak travelDiary := inferInstance

example : Subschema waterfall travelDiary := inferInstance

def Subschema.same : (s : Schema)  → Subschema s s
  | [] => .done
  | _ :: cs => .keep (same cs)

def Row.project : Row s → (s' : Schema) → Subschema s s' → Row s'
  | .nil, [], .done => .nil
  | .cons v r, _, .keep sub => .cons v (project r _ sub)
  | .cons _ r, _, .drop sub => project r _ sub

class inductive Col : Schema → String → outParam DBType → Type where
  | here : Col (⟨name, t⟩ :: _) name t
  | there : Col s name t → Col (_ :: s) name t

instance : Col (⟨name, t⟩ :: s) name t := .here
instance [foundAt : Col s name t] : Col (c :: s) name t := .there foundAt

example : Col [⟨"hi", .base .bool⟩] "hi" (.base .bool) := inferInstance
example : Col [⟨"other", .base .int⟩, ⟨"hi", .base .bool⟩] "hi" (.base .bool) := inferInstance

inductive Expr : Schema → DBType → Type where
  | col (n : String) (loc : Col s n t) : Expr s t
  | eq (e1 e2 : Expr s t) : Expr s (.base .bool)
  | lt (e1 e2 : Expr s (.base .int)) : Expr s (.base .bool)
  | and (e1 e2 : Expr s (.base .bool)) : Expr s (.base .bool)
  | const : t.asType → Expr s t

def Row.get : Col s n t → Row s → t.asType
  | .here, .cons v _ => v
  | .there next, .cons _ r => get next r


def Expr.evaluate (row : Row s) : Expr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2  => evaluate row e1 == evaluate row e2
  | .lt e1 e2  => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v

inductive RelAlg : Schema → Type where
  | table : Table s → RelAlg s
  | union : RelAlg s → RelAlg s → RelAlg s
  | diff : RelAlg s → RelAlg s → RelAlg s
  | select : RelAlg s → Expr s (.base .bool) → RelAlg s
  | project : RelAlg s → Subschema s s' → RelAlg s'

def List.without [BEq α] : List α → List α → List α
  | [], _ => []
  | x::xs, banned =>
    if banned.contains x then
      without xs banned
    else
       x :: without xs banned

def RelAlg.exec : RelAlg s → Table s
  | .table t => t
  | .union r1 r2 => exec r1 ++ exec r2
  | .diff r1 r2 => (exec r1).without (exec r2)
  | .select r e => (exec r).filter fun row => e.evaluate row
  | .project r sub => exec r |>.map (·.project _ sub)

def elevation [Subschema s [⟨"elevation", .base .int⟩]] : Subschema s [⟨"elevation", .base .int⟩] := inferInstance

open RelAlg in
def example1 :=
  table mountainDiary |>.select (.lt (.const 500) (.col "elevation" inferInstance)) |>.project elevation

#eval example1.exec
