import ExampleSupport
import Examples.DependentTypes

set_option linter.unusedVariables false

-- ANCHOR: DBType
inductive DBType where
  | int | string | bool

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
-- ANCHOR_END: DBType

/-- info:
"Mount Hood"
-/
#check_msgs in
-- ANCHOR: mountHoodEval
#eval ("Mount Hood" : DBType.string.asType)
-- ANCHOR_END: mountHoodEval

discarding
/--
error: failed to synthesize
  BEq t.asType

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: dbEqNoSplit
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  x == y
-- ANCHOR_END: dbEqNoSplit
stop discarding

-- ANCHOR: dbEq
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
-- ANCHOR_END: dbEq


-- ANCHOR: BEqDBType
instance {t : DBType} : BEq t.asType where
  beq := t.beq
-- ANCHOR_END: BEqDBType


-- ANCHOR: BEqDBTypeCodes
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
-- ANCHOR_END: BEqDBTypeCodes


-- ANCHOR: ReprAsType
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
-- ANCHOR_END: ReprAsType


-- ANCHOR: Schema
structure Column where
  name : String
  contains : DBType

abbrev Schema := List Column
-- ANCHOR_END: Schema



-- ANCHOR: Row
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
-- ANCHOR_END: Row

-- ANCHOR: RowStuck
example (c cs) := Row (c :: cs)
-- ANCHOR_END: RowStuck

-- ANCHOR: Naturals
section
example := Nat
open Nat
example := succ
example := zero
end
-- ANCHOR_END: Naturals

-- ANCHOR: Table
abbrev Table (s : Schema) := List (Row s)
-- ANCHOR_END: Table


-- ANCHOR: peak
abbrev peak : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"elevation", .int⟩,
  ⟨"lastVisited", .int⟩
]
-- ANCHOR_END: peak


-- ANCHOR: mountainDiary
def mountainDiary : Table peak := [
  ("Mount Nebo",       "USA",     3637, 2013),
  ("Moscow Mountain",  "USA",     1519, 2015),
  ("Himmelbjerget",    "Denmark",  147, 2004),
  ("Mount St. Helens", "USA",     2549, 2010)
]
-- ANCHOR_END: mountainDiary


-- ANCHOR: waterfall
abbrev waterfall : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"lastVisited", .int⟩
]
-- ANCHOR_END: waterfall


-- ANCHOR: waterfallDiary
def waterfallDiary : Table waterfall := [
  ("Multnomah Falls", "USA", 2018),
  ("Shoshone Falls",  "USA", 2014)
]
-- ANCHOR_END: waterfallDiary

discarding
/--
error: Type mismatch
  (v1, r1')
has type
  ?m.10 × ?m.11
but is expected to have type
  Row (col :: cols)
-/
#check_msgs in
-- ANCHOR: RowBEqRecursion
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | col::cols =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
-- ANCHOR_END: RowBEqRecursion
stop discarding


-- ANCHOR: RowBEq
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'

instance : BEq (Row s) where
  beq := Row.bEq
-- ANCHOR_END: RowBEq


-- ANCHOR: HasCol
inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
-- ANCHOR_END: HasCol

-- ANCHOR: peakElevationInt
example : HasCol peak "elevation" .int := .there (.there .here)
-- ANCHOR_END: peakElevationInt


-- ANCHOR: Rowget
def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next
-- ANCHOR_END: Rowget



-- ANCHOR: Subschema
inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger
-- ANCHOR_END: Subschema

-- ANCHOR: SubschemaNames
example := @Subschema.nil
example := @Subschema.cons
example := @HasCol.there
example := @HasCol.here
example := HasCol peak "location" DBType.string
example := Subschema peak []
-- ANCHOR_END: SubschemaNames

-- ANCHOR: travelDiary
abbrev travelDiary : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]
-- ANCHOR_END: travelDiary

-- ANCHOR: peakDiarySub
example : Subschema travelDiary peak :=
  .cons .here
    (.cons (.there .here)
      (.cons (.there (.there (.there .here))) .nil))
-- ANCHOR_END: peakDiarySub


-- ANCHOR: emptySub
example : Subschema [] peak := by constructor
-- ANCHOR_END: emptySub


/-- error:
unsolved goals
case a
⊢ HasCol peak "location" DBType.string

case a
⊢ Subschema [] peak
-/
#check_msgs in
-- ANCHOR: notDone
example : Subschema [⟨"location", .string⟩] peak := by constructor
-- ANCHOR_END: notDone


/-- error:
unsolved goals
case a.a
⊢ HasCol
    [{ name := "location", contains := DBType.string }, { name := "elevation", contains := DBType.int },
      { name := "lastVisited", contains := DBType.int }]
    "location" DBType.string

case a
⊢ Subschema [] peak
-/
#check_msgs in
-- ANCHOR: notDone2
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
-- ANCHOR_END: notDone2


/-- error:
unsolved goals
case a
⊢ Subschema [] peak
-/
#check_msgs in
-- ANCHOR: notDone3
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
  constructor
-- ANCHOR_END: notDone3




-- ANCHOR: notDone4
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
  constructor
  constructor
-- ANCHOR_END: notDone4


-- ANCHOR: notDone5
example : Subschema [⟨"location", .string⟩] peak :=
  .cons (.there .here) .nil
-- ANCHOR_END: notDone5


-- ANCHOR: notDone6
example : Subschema [⟨"location", .string⟩] peak := by repeat constructor
-- ANCHOR_END: notDone6


-- ANCHOR: subschemata
example : Subschema travelDiary peak := by repeat constructor

example : Subschema travelDiary waterfall := by repeat constructor
-- ANCHOR_END: subschemata


-- ANCHOR: SubschemaAdd
def Subschema.addColumn :
    Subschema smaller bigger →
    Subschema smaller (c :: bigger)
  | .nil  => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn
-- ANCHOR_END: SubschemaAdd


-- ANCHOR: SubschemaSame
def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn
-- ANCHOR_END: SubschemaSame


-- ANCHOR: addVal
def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')
-- ANCHOR_END: addVal

-- ANCHOR: RowProj
def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)
-- ANCHOR_END: RowProj

-- ANCHOR: DBExpr
inductive DBExpr (s : Schema) : DBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t
  | eq (e1 e2 : DBExpr s t) : DBExpr s .bool
  | lt (e1 e2 : DBExpr s .int) : DBExpr s .bool
  | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
  | const : t.asType → DBExpr s t
-- ANCHOR_END: DBExpr

namespace Fake
-- ANCHOR: tallDk
def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (.col "elevation" (by repeat constructor)))
       (.eq (.col "location" (by repeat constructor)) (.const "Denmark"))
-- ANCHOR_END: tallDk
end Fake

-- ANCHOR: cBang
macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))
-- ANCHOR_END: cBang

-- ANCHOR: tallDkBetter
def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (c! "elevation"))
       (.eq (c! "location") (.const "Denmark"))
-- ANCHOR_END: tallDkBetter


-- ANCHOR: DBExprEval
def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2  => evaluate row e1 == evaluate row e2
  | .lt e1 e2  => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v
-- ANCHOR_END: DBExprEval

-- ANCHOR: DBExprEvalType
example : Row s → DBExpr s t → t.asType := DBExpr.evaluate
-- ANCHOR_END: DBExprEvalType

/-- info:
false
-/
#check_msgs in
-- ANCHOR: valbybakke
#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
-- ANCHOR_END: valbybakke


/-- info:
true
-/
#check_msgs in
-- ANCHOR: fakeDkBjerg
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)
-- ANCHOR_END: fakeDkBjerg


/-- info:
false
-/
#check_msgs in
-- ANCHOR: borah
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)
-- ANCHOR_END: borah


-- ANCHOR: disjoint
def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)
-- ANCHOR_END: disjoint


-- ANCHOR: renameColumn
def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'
-- ANCHOR_END: renameColumn

-- ANCHOR: Query
inductive Query : Schema → Type where
  | table : Table s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → DBExpr s .bool → Query s
  | project :
    Query s → (s' : Schema) →
    Subschema s' s →
    Query s'
  | product :
    Query s1 → Query s2 →
    disjoint (s1.map Column.name) (s2.map Column.name) →
    Query (s1 ++ s2)
  | renameColumn :
    Query s → (c : HasCol s n t) → (n' : String) →
    !((s.map Column.name).contains n') →
    Query (s.renameColumn c n')
  | prefixWith :
    (n : String) → Query s →
    Query (s.map fun c => {c with name := n ++ "." ++ c.name})
-- ANCHOR_END: Query


-- ANCHOR: RowAppend
def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)
-- ANCHOR_END: RowAppend


namespace Mine
-- ANCHOR: ListFlatMap
def List.flatMap (f : α → List β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x ++ xs.flatMap f
-- ANCHOR_END: ListFlatMap
end Mine

-- ANCHOR: TableCartProd
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) :=
  table1.flatMap fun r1 => table2.map r1.append
-- ANCHOR_END: TableCartProd

namespace OrElse
-- ANCHOR: TableCartProdOther
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) := Id.run do
  let mut out : Table (s1 ++ s2) := []
  for r1 in table1 do
    for r2 in table2 do
      out := (r1.append r2) :: out
  pure out.reverse
-- ANCHOR_END: TableCartProdOther
end OrElse

-- ANCHOR: filterA
example : (
["Willamette", "Columbia", "Sandy", "Deschutes"].filter (·.length > 8)
) = (
["Willamette", "Deschutes"]
) := rfl
-- ANCHOR_END: filterA



-- ANCHOR: ListWithout
def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)
-- ANCHOR_END: ListWithout


-- ANCHOR: renameRow
def Row.rename (c : HasCol s n t) (row : Row s) :
    Row (s.renameColumn c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal v (r.rename next)
-- ANCHOR_END: renameRow


-- ANCHOR: prefixRow
def prefixRow (row : Row s) :
    Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)
-- ANCHOR_END: prefixRow



-- ANCHOR: QueryExec
def Query.exec : Query s → Table s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => exec q1 |>.without (exec q2)
-- ANCHOR: selectCase
  | .select q e => exec q |>.filter e.evaluate
-- ANCHOR_END: selectCase
  | .project q _ sub => exec q |>.map (·.project _ sub)
  | .product q1 q2 _ => exec q1 |>.cartesianProduct (exec q2)
  | .renameColumn q c _ _ => exec q |>.map (·.rename c)
  | .prefixWith _ q => exec q |>.map prefixRow
-- ANCHOR_END: QueryExec


-- ANCHOR: Query1
open Query in
def example1 :=
  table mountainDiary |>.select
  (.lt (.const 500) (c! "elevation")) |>.project
  [⟨"elevation", .int⟩] (by repeat constructor)
-- ANCHOR_END: Query1


/-- info:
[3637, 1519, 2549]
-/
#check_msgs in
-- ANCHOR: Query1Exec
#eval example1.exec
-- ANCHOR_END: Query1Exec

-- ANCHOR: Query2
open Query in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfall := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfall (by decide)
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
-- ANCHOR_END: Query2


/-- info:
[("Mount Nebo", "Multnomah Falls"), ("Mount Nebo", "Shoshone Falls"), ("Moscow Mountain", "Multnomah Falls"),
  ("Moscow Mountain", "Shoshone Falls"), ("Mount St. Helens", "Multnomah Falls"),
  ("Mount St. Helens", "Shoshone Falls")]
-/
#check_msgs in
-- ANCHOR: Query2Exec
#eval example2.exec
-- ANCHOR_END: Query2Exec

namespace Ooops

discarding
/--
error: unsolved goals
mountains : Query (List.map (fun c => { name := "mountain" ++ "." ++ c.name, contains := c.contains }) peak) :=
  prefixWith "mountain" (table mountainDiary)
waterfalls : Query (List.map (fun c => { name := "waterfall" ++ "." ++ c.name, contains := c.contains }) waterfall) :=
  prefixWith "waterfall" (table waterfallDiary)
⊢ disjoint ["mountain.name", "mountain.location", "mountain.elevation", "mountain.lastVisited"]
      ["waterfall.name", "waterfall.location", "waterfall.lastVisited"] =
    true
---
error: unsolved goals
case a.a.a.a.a.a.a
mountains : Query (List.map (fun c => { name := "mountain" ++ "." ++ c.name, contains := c.contains }) peak) := ⋯
waterfalls : Query (List.map (fun c => { name := "waterfall" ++ "." ++ c.name, contains := c.contains }) waterfall) := ⋯
⊢ HasCol (List.map (fun c => { name := "waterfall" ++ "." ++ c.name, contains := c.contains }) []) "location" ?m.62066
-/
#check_msgs in
-- ANCHOR: QueryOops1
open Query in
def example2 :=
  let mountains := table mountainDiary |>.prefixWith "mountain"
  let waterfalls := table waterfallDiary |>.prefixWith "waterfall"
  mountains.product waterfalls (by simp)
    |>.select (.eq (c! "location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
-- ANCHOR_END: QueryOops1
stop discarding

/--
error: Tactic `decide` proved that the proposition
  disjoint (List.map Column.name peak) (List.map Column.name waterfall) = true
is false
---
error: unsolved goals
case a.a.a.a.a.a.a
mountains : Query peak := ⋯
waterfalls : Query waterfall := ⋯
⊢ HasCol [] "mountain.location" ?m.29
---
error: unsolved goals
case a.a.a.a.a.a.a
mountains : Query peak := ⋯
waterfalls : Query waterfall := ⋯
⊢ HasCol [] "waterfall.location" ?m.29
---
error: unsolved goals
case a.a.a.a.a.a.a.a
mountains : Query peak := ⋯
waterfalls : Query waterfall := ⋯
⊢ HasCol [] "mountain.name" DBType.string

case a
mountains : Query peak := ⋯
waterfalls : Query waterfall := ⋯
⊢ Subschema [{ name := "waterfall.name", contains := DBType.string }] (peak ++ waterfall)
-/
#check_msgs in
-- ANCHOR: QueryOops2
open Query in
def example2 :=
  let mountains := table mountainDiary
  let waterfalls := table waterfallDiary
  mountains.product waterfalls (by decide)
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
-- ANCHOR_END: QueryOops2
end Ooops

#eval (by repeat constructor : Nat)
#eval (by repeat constructor : List Nat)
#eval (by repeat constructor : Vect Nat 4)
#eval (by repeat constructor : Row [⟨"price", .int⟩])
#eval (by repeat constructor : Row peak)
deriving instance Repr for HasCol
#eval (by repeat constructor : HasCol [⟨"price", .int⟩, ⟨"price", .int⟩] "price" .int)


-- ANCHOR: nullable
structure NDBType where
  underlying : DBType
  nullable : Bool

abbrev NDBType.asType (t : NDBType) : Type :=
  if t.nullable then
    Option t.underlying.asType
  else
    t.underlying.asType
-- ANCHOR_END: nullable

-- ANCHOR: misc
example := List Bool
example := false
example := true
example := Prop
example := @List.filter
example := @List.map
section
variable {smaller bigger : Schema}
example := Subschema smaller bigger
example := (smaller, bigger)
end
example := [List Nat, Vect Nat 4, Row [], Row [⟨"price", .int⟩], Row peak, HasCol [⟨"price", .int⟩, ⟨"price", .int⟩] "price" .int]
-- ANCHOR_END: misc

discarding
-- ANCHOR: ListMonad
instance : Monad List where
  pure x := [x]
  bind xs f := List.flatMap f xs
-- ANCHOR_END: ListMonad
stop discarding
