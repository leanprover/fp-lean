import Examples.Support
import Examples.DependentTypes


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
  def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
    x == y
message
"failed to synthesize instance
  BEq (asType t)"
end expect


book declaration {{{ dbEq }}}
  def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
    match t with
    | .int => x == y
    | .string => x == y
    | .bool => x == y
stop book declaration


book declaration {{{ BEqDBType }}}
  instance {t : DBType} : BEq t.asType where
    beq := t.beq
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



book declaration {{{ Row }}}
  abbrev Row : Schema → Type
    | [] => Unit
    | [col] => col.contains.asType
    | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
stop book declaration




book declaration {{{ Table }}}
  abbrev Table (s : Schema) := List (Row s)
stop book declaration


book declaration {{{ peak }}}
  abbrev peak : Schema := [
    ⟨"name", DBType.string⟩,
    ⟨"location", DBType.string⟩,
    ⟨"elevation", DBType.int⟩,
    ⟨"lastVisited", .int⟩
  ]
stop book declaration


book declaration {{{ mountainDiary }}}
  def mountainDiary : Table peak := [
    ("Mount Nebo",       "USA",     3637, 2013),
    ("Moscow Mountain",  "USA",     1519, 2015),
    ("Himmelbjerget",    "Denmark",  147, 2004),
    ("Mount St. Helens", "USA",     2549, 2010)
  ]
stop book declaration


book declaration {{{ waterfall }}}
  abbrev waterfall : Schema := [
    ⟨"name", .string⟩,
    ⟨"location", .string⟩,
    ⟨"lastVisited", .int⟩
  ]
stop book declaration


book declaration {{{ waterfallDiary }}}
  def waterfallDiary : Table waterfall := [
    ("Multnomah Falls", "USA", 2018),
    ("Shoshone Falls",  "USA", 2014)
  ]
stop book declaration


expect error {{{ RowBEqRecursion }}}
  def Row.bEq (r1 r2 : Row s) : Bool :=
    match s with
    | [] => true
    | col::cols =>
      match r1, r2 with
      | (v1, r1'), (v2, r2') =>
        v1 == v2 && bEq r1' r2'
message
"type mismatch
  (v1, r1')
has type
  ?m.6559 × ?m.6562 : Type (max ?u.6571 ?u.6570)
but is expected to have type
  Row (col :: cols) : Type"
end expect



book declaration {{{ RowBEq }}}
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
stop book declaration


book declaration {{{ HasCol }}}
  inductive HasCol : Schema → String → DBType → Type where
    | here : HasCol (⟨name, t⟩ :: _) name t
    | there : HasCol s name t → HasCol (_ :: s) name t
stop book declaration

bookExample type {{{ peakElevationInt }}}
  .there (.there .here)
  <===
  HasCol peak "elevation" .int
end bookExample


book declaration {{{ Rowget }}}
  def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
    match s, col, row with
    | [_], .here, v => v
    | _::_::_, .here, (v, _) => v
    | _::_::_, .there next, (_, r) => get r next
stop book declaration



book declaration {{{ Subschema }}}
  inductive Subschema : Schema → Schema → Type where
    | nil : Subschema [] bigger
    | cons :
        HasCol bigger n t →
        Subschema smaller bigger →
        Subschema (⟨n, t⟩ :: smaller) bigger
stop book declaration

book declaration {{{ travelDiary }}}
  abbrev travelDiary : Schema :=
    [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]
stop book declaration

book declaration {{{ peakDiarySub }}}
  example : Subschema travelDiary peak :=
    .cons .here
      (.cons (.there .here)
        (.cons (.there (.there (.there .here))) .nil))
stop book declaration


book declaration {{{ emptySub }}}
  example : Subschema [] peak := by constructor
stop book declaration


expect error {{{ notDone }}}
  example : Subschema [⟨"location", .string⟩] peak := by constructor
message
"unsolved goals
case a
⊢ HasCol peak \"location\" DBType.string

case a
⊢ Subschema [] peak"
end expect


expect error {{{ notDone2 }}}
  example : Subschema [⟨"location", .string⟩] peak := by
    constructor
    constructor
message
"unsolved goals
case a.a
⊢ HasCol
    [{ name := \"location\", contains := DBType.string }, { name := \"elevation\", contains := DBType.int },
      { name := \"lastVisited\", contains := DBType.int }]
    \"location\" DBType.string

case a
⊢ Subschema [] peak"
end expect


expect error {{{ notDone3 }}}
  example : Subschema [⟨"location", .string⟩] peak := by
    constructor
    constructor
    constructor
message
"unsolved goals
case a
⊢ Subschema [] peak"
end expect




book declaration {{{ notDone4 }}}
  example : Subschema [⟨"location", .string⟩] peak := by
    constructor
    constructor
    constructor
    constructor
stop book declaration


book declaration {{{ notDone5 }}}
  example : Subschema [⟨"location", .string⟩] peak :=
    .cons (.there .here) .nil
stop book declaration


book declaration {{{ notDone6 }}}
  example : Subschema [⟨"location", .string⟩] peak := by repeat constructor
stop book declaration


book declaration {{{ subschemata }}}
  example : Subschema travelDiary peak := by repeat constructor

  example : Subschema travelDiary waterfall := by repeat constructor
stop book declaration


book declaration {{{ SubschemaAdd }}}
  def Subschema.addColumn (sub : Subschema smaller bigger) : Subschema smaller (c :: bigger) :=
    match sub with
    | .nil  => .nil
    | .cons col sub' => .cons (.there col) sub'.addColumn
stop book declaration


book declaration {{{ SubschemaSame }}}
  def Subschema.reflexive : (s : Schema) → Subschema s s
    | [] => .nil
    | _ :: cs => .cons .here (reflexive cs).addColumn
stop book declaration


book declaration {{{ addVal }}}
  def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
    match s, row with
    | [], () => v
    | c' :: cs, v' => (v, v')
stop book declaration

book declaration {{{ RowProj }}}
  def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
    | [], .nil => ()
    | [_], .cons c .nil => row.get c
    | _::_::_, .cons c cs => (row.get c, row.project _ cs)
stop book declaration

book declaration {{{ DBExpr }}}
  inductive DBExpr (s : Schema) : DBType → Type where
    | col (n : String) (loc : HasCol s n t) : DBExpr s t
    | eq (e1 e2 : DBExpr s t) : DBExpr s .bool
    | lt (e1 e2 : DBExpr s .int) : DBExpr s .bool
    | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
    | const : t.asType → DBExpr s t
stop book declaration

namespace Fake
book declaration {{{ tallDk }}}
  def tallInDenmark : DBExpr peak .bool :=
    .and (.lt (.const 1000) (.col "elevation" (by repeat constructor)))
         (.eq (.col "location" (by repeat constructor)) (.const "Denmark"))
stop book declaration
end Fake

book declaration {{{ cBang }}}
  macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))
stop book declaration

book declaration {{{ tallDkBetter }}}
  def tallInDenmark : DBExpr peak .bool :=
    .and (.lt (.const 1000) (c! "elevation"))
         (.eq (c! "location") (.const "Denmark"))
stop book declaration


book declaration {{{ DBExprEval }}}
  def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
    | .col _ loc => row.get loc
    | .eq e1 e2  => evaluate row e1 == evaluate row e2
    | .lt e1 e2  => evaluate row e1 < evaluate row e2
    | .and e1 e2 => evaluate row e1 && evaluate row e2
    | .const v => v
stop book declaration

expect info {{{ valbybakke }}}
  #eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
message
"false"
end expect


expect info {{{ fakeDkBjerg }}}
  #eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)
message
"true"
end expect


expect info {{{ borah }}}
  #eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)
message
"false"
end expect


book declaration {{{ disjoint }}}
  def disjoint [BEq α] (xs ys : List α) : Bool :=
    not (xs.any ys.contains || ys.any xs.contains)
stop book declaration


book declaration {{{ renameColumn }}}
  def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
    | c :: cs, .here, n' => {c with name := n'} :: cs
    | c :: cs, .there next, n' => c :: renameColumn cs next n'
stop book declaration

book declaration {{{ Query }}}
  inductive Query : Schema → Type where
    | table : Table s → Query s
    | union : Query s → Query s → Query s
    | diff : Query s → Query s → Query s
    | select : Query s → DBExpr s .bool → Query s
    | project : Query s → (s' : Schema) → Subschema s' s → Query s'
    | product :
        Query s1 → Query s2 →
        disjoint (s1.map Column.name) (s2.map Column.name) →
        Query (s1 ++ s2)
    | renameColumn :
        Query s → (c : HasCol s n t) → (n' : String) → !((s.map Column.name).contains n') →
        Query (s.renameColumn c n')
    | prefixWith :
        (n : String) → Query s →
        Query (s.map fun c => {c with name := n ++ "." ++ c.name})
stop book declaration


book declaration {{{ RowAppend }}}
  def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
    match s1, r1 with
    | [], () => r2
    | [_], v => addVal v r2
    | _::_::_, (v, r') => (v, r'.append r2)
stop book declaration


book declaration {{{ ListFlatMap }}}
  def List.flatMap (f : α → List β) : (xs : List α) → List β
    | [] => []
    | x :: xs => f x ++ xs.flatMap f
stop book declaration


book declaration {{{ TableCartProd }}}
  def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) : Table (s1 ++ s2) :=
    table1.flatMap fun r1 => table2.map r1.append
stop book declaration

namespace OrElse
book declaration {{{ TableCartProdOther }}}
  def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) : Table (s1 ++ s2) := Id.run do
    let mut out : Table (s1 ++ s2) := []
    for r1 in table1 do
      for r2 in table2 do
        out := (r1.append r2) :: out
    pure out.reverse
stop book declaration
end OrElse

bookExample {{{ filterA }}}
  ["Willamette", "Columbia", "Sandy", "Deschutes"].filter (·.length > 8)
  ===>
  ["Willamette", "Deschutes"]
end bookExample



book declaration {{{ ListWithout }}}
  def List.without [BEq α] (source banned : List α) : List α :=
    source.filter fun r => !(banned.contains r)
stop book declaration


book declaration {{{ renameRow }}}
  def Row.rename (c : HasCol s n t) (row : Row s) : Row (s.renameColumn c n') :=
    match s, row, c with
    | [_], v, .here => v
    | _::_::_, (v, r), .here => (v, r)
    | _::_::_, (v, r), .there next => addVal v (r.rename next)
stop book declaration


book declaration {{{ prefixRow }}}
  def prefixRow (row : Row s) : Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
    match s, row with
    | [], _ => ()
    | [_], v => v
    | _::_::_, (v, r) => (v, prefixRow r)
stop book declaration



book declaration {{{ QueryExec }}}
  def Query.exec : Query s → Table s
    | .table t => t
    | .union q1 q2 => exec q1 ++ exec q2
    | .diff q1 q2 => exec q1 |>.without (exec q2)
    | .select q e => exec q |>.filter e.evaluate
    | .project q _ sub => exec q |>.map (·.project _ sub)
    | .product q1 q2 _ => exec q1 |>.cartesianProduct (exec q2)
    | .renameColumn q c _ _ => exec q |>.map (·.rename c)
    | .prefixWith _ q => exec q |>.map prefixRow
stop book declaration


book declaration {{{ Query1 }}}
open Query in
def example1 :=
  table mountainDiary |>.select
  (.lt (.const 500) (c! "elevation")) |>.project
  [⟨"elevation", .int⟩] (by repeat constructor)
stop book declaration


expect info {{{ Query1Exec }}}
  #eval example1.exec
message
"[3637, 1519, 2549]"
end expect

book declaration {{{ Query2 }}}
open Query in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfall := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfall (by simp)
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩] (by repeat constructor)
stop book declaration


expect info {{{ Query2Exec }}}
  #eval example2.exec
message
"[(\"Mount Nebo\", \"Multnomah Falls\"),
 (\"Mount Nebo\", \"Shoshone Falls\"),
 (\"Moscow Mountain\", \"Multnomah Falls\"),
 (\"Moscow Mountain\", \"Shoshone Falls\"),
 (\"Mount St. Helens\", \"Multnomah Falls\"),
 (\"Mount St. Helens\", \"Shoshone Falls\")]"
end expect

namespace Ooops


expect error {{{ QueryOops1 }}}
  open Query in
  def example2 :=
    let mountains := table mountainDiary |>.prefixWith "mountain"
    let waterfalls := table waterfallDiary |>.prefixWith "waterfall"
    mountains.product waterfalls (by simp)
      |>.select (.eq (c! "location") (c! "waterfall.location"))
      |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩] (by repeat constructor)
message
"unsolved goals
case a.a.a.a.a.a.a
mountains : Query (List.map (fun c => { name := \"mountain\" ++ \".\" ++ c.name, contains := c.contains }) peak) :=
  prefixWith \"mountain\" (table mountainDiary)
waterfalls : Query (List.map (fun c => { name := \"waterfall\" ++ \".\" ++ c.name, contains := c.contains }) waterfall) :=
  prefixWith \"waterfall\" (table waterfallDiary)
⊢ HasCol (List.map (fun c => { name := \"waterfall\" ++ \".\" ++ c.name, contains := c.contains }) []) \"location\" ?m.109970"
end expect

expect error {{{ QueryOops2 }}}
  open Query in
  def example2 :=
    let mountains := table mountainDiary
    let waterfalls := table waterfallDiary
    mountains.product waterfalls (by simp)
      |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
      |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩] (by repeat constructor)
message
"unsolved goals
mountains : Query peak := table mountainDiary
waterfalls : Query waterfall := table waterfallDiary
⊢ False"
end expect
end Ooops

#eval (by repeat constructor : Nat)
#eval (by repeat constructor : List Nat)
#eval (by repeat constructor : Vect Nat 4)
#eval (by repeat constructor : Row [⟨"price", .int⟩])
#eval (by repeat constructor : Row peak)
deriving instance Repr for HasCol
#eval (by repeat constructor : HasCol [⟨"price", .int⟩, ⟨"price", .int⟩] "price" .int)
