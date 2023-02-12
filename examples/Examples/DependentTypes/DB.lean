import Examples.Support


book declaration {{{ DBType }}}
  inductive DBType where
    | int | string | bool

  abbrev DBType.asType : DBType → Type
    | .int => Int
    | .string => String
    | .bool => Bool
stop book declaration

expect info {{{ mountHoodEval }}}
  #eval ("Mount Hood" : DBType.string.asType)
message
"\"Mount Hood\""
end expect


expect error {{{ dbEqNoSplit }}}
  def dbEq (t : DBType) (x y : t.asType) : Bool :=
    x == y
message
"failed to synthesize instance
  BEq (DBType.asType t)"
end expect


book declaration {{{ dbEq }}}
  def dbEq (t : DBType) (x y : t.asType) : Bool :=
    match t with
    | .int => x == y
    | .string => x == y
    | .bool => x == y
stop book declaration


book declaration {{{ BEqDBType }}}
  instance {t : DBType} : BEq t.asType where
    beq := dbEq t
stop book declaration


book declaration {{{ BEqDBTypeCodes }}}
  instance : BEq DBType where
    beq
      | .int, .int => true
      | .string, .string => true
      | .bool, .bool => true
      | _, _ => false
stop book declaration


book declaration {{{ ReprAsType }}}
  instance {t : DBType} : Repr t.asType where
    reprPrec :=
      match t with
      | .int => reprPrec
      | .string => reprPrec
      | .bool => reprPrec
stop book declaration


book declaration {{{ Schema }}}
  structure Column where
    name : String
    contains : DBType

  abbrev Schema := List Column
stop book declaration

inductive Row : Schema → Type where
  | nil : Row []
  | cons : c.contains.asType → Row cols → Row (c :: cols)
deriving Repr

def Row.bEq : (r1 r2 : Row s) → Bool
  | .nil, .nil => true
  | .cons v1 r1, .cons v2 r2 => v1 == v2 && bEq r1 r2

instance : BEq (Row s) where
  beq := Row.bEq

abbrev Table (s : Schema) := List (Row s)

abbrev peak : Schema :=
  [⟨"name", DBType.string⟩, ⟨"location", DBType.string⟩, ⟨"elevation", DBType.int⟩, ⟨"lastVisited", .int⟩]

def mountainDiary : Table peak := [
  .cons "Mount Nebo"       <| .cons "USA"     <| .cons 3637 <| .cons 2013 .nil,
  .cons "Moscow Mountain"  <| .cons "USA"     <| .cons 1519 <| .cons 2015 .nil,
  .cons "Himmelbjerget"    <| .cons "Denmark" <| .cons  147 <| .cons 2004 .nil,
  .cons "Mount St. Helens" <| .cons "USA"     <| .cons 2549 <| .cons 2010 .nil
]

abbrev waterfall : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]

def waterfallDiary : Table waterfall := [
  .cons "Multnomah Falls" <| .cons "USA" <| .cons 2018 .nil,
  .cons "Shoshone Falls"  <| .cons "USA" <| .cons 2014 .nil
]

class inductive Subschema : Schema → Schema → Type where
  | keep : Subschema bigger smaller → Subschema (c :: bigger) (c :: smaller)
  | drop : Subschema bigger smaller → Subschema (c :: bigger) smaller
  | done : Subschema [] []

instance [inst : Subschema bigger smaller] : Subschema (c :: bigger) (c :: smaller) := .keep inst
instance [inst : Subschema bigger smaller] : Subschema (c :: bigger) smaller := .drop inst
instance : Subschema [] [] := .done

abbrev travelDiary : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]

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

example : Col [⟨"hi", .bool⟩] "hi" .bool := inferInstance
example : Col [⟨"other", .int⟩, ⟨"hi", .bool⟩] "hi" .bool := inferInstance

inductive Cond : Schema → DBType → Type where
  | col (n : String) (loc : Col s n t) : Cond s t
  | eq (e1 e2 : Cond s t) : Cond s .bool
  | lt (e1 e2 : Cond s .int) : Cond s .bool
  | and (e1 e2 : Cond s .bool) : Cond s .bool
  | const : t.asType → Cond s t

def Row.get : Col s n t → Row s → t.asType
  | .here, .cons v _ => v
  | .there next, .cons _ r => get next r


def Cond.evaluate (row : Row s) : Cond s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2  => evaluate row e1 == evaluate row e2
  | .lt e1 e2  => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v

def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)

def renameSchema : (s : Schema) → Col s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameSchema cs next n'

inductive RelAlg : Schema → Type where
  | table : Table s → RelAlg s
  | union : RelAlg s → RelAlg s → RelAlg s
  | diff : RelAlg s → RelAlg s → RelAlg s
  | select : RelAlg s → Cond s .bool → RelAlg s
  | project : RelAlg s → Subschema s s' → RelAlg s'
  | product :
      RelAlg s1 → RelAlg s2 →
      disjoint (s1.map Column.name) (s2.map Column.name) →
      RelAlg (s1 ++ s2)
  | rename :
      RelAlg s → (c : Col s n t) → (n' : String) →
      RelAlg (renameSchema s c n')
  | prefixWith :
      (n : String) → RelAlg s →
      RelAlg (s.map fun c => {c with name := n ++ "." ++ c.name})

def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match r1 with
  | .nil => r2
  | .cons v r' => .cons v (append r' r2)

def List.flatMap : (xs : List α) → (f : α → List β) → List β
  | [], f => []
  | x :: xs, f=> f x ++ flatMap xs f

def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) : Table (s1 ++ s2) :=
  table1.flatMap fun r1 => table2.map r1.append

def List.without [BEq α] : List α → List α → List α
  | [], _ => []
  | x::xs, banned =>
    if banned.contains x then
      without xs banned
    else
       x :: without xs banned

def renameRow : Row s → (c : Col s n t) → Row (renameSchema s c n')
  | .cons v r, .here => .cons v r
  | .cons v r, .there next => .cons v (renameRow r next)

def renameTable (table : Table s) (c : Col s n t) : Table (renameSchema s c n') :=
  table.map (renameRow · c)

def prefixRow : Row s → Row (s.map fun c => {c with name := n ++ "." ++ c.name})
  | .nil => .nil
  | .cons v r => .cons v (prefixRow r)

def prefixTable (t : Table s) : Table (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  t.map prefixRow



def RelAlg.exec : RelAlg s → Table s
  | .table t => t
  | .union r1 r2 => exec r1 ++ exec r2
  | .diff r1 r2 => exec r1 |>.without (exec r2)
  | .select r e => (exec r).filter fun row => e.evaluate row
  | .project r sub => exec r |>.map (·.project _ sub)
  | .product r1 r2 _ => exec r1 |>.cartesianProduct (exec r2)
  | .rename r c n' => renameTable (exec r) c
  | .prefixWith n r => prefixTable (n := n) (exec r)

def elevation [Subschema s [⟨"elevation", .int⟩]] : Subschema s [⟨"elevation", .int⟩] := inferInstance

open RelAlg in
def example1 :=
  table mountainDiary |>.select (.lt (.const 500) (.col "elevation" inferInstance)) |>.project elevation

#eval example1.exec

def names [Subschema s [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]] : Subschema s [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩] := inferInstance

open RelAlg in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfall := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfall (by simp)
    |>.select (.eq (.col "mountain.location" (by repeat constructor)) (.col "waterfall.location" (by repeat constructor)))
    |>.project (s' := [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]) (by repeat constructor)

#eval example2.exec
