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
  abbrev peak : Schema :=
    [⟨"name", DBType.string⟩, ⟨"location", DBType.string⟩, ⟨"elevation", DBType.int⟩, ⟨"lastVisited", .int⟩]
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
  abbrev waterfall : Schema :=
    [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]
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
      | (v1, r1'), (v2, r2') => _
message
"type mismatch
  (v1, r1')
has type
  ?m.6647 × ?m.6650 : Type (max ?u.6659 ?u.6658)
but is expected to have type
  Row (col :: cols) : Type"
end expect



book declaration {{{ RowBEq }}}
  def Row.bEq (r1 r2 : Row s) : Bool :=
    match s with
    | [] => true
    | [_] => r1 == r2
    | _::col2::cols => r1.fst == r2.fst && bEq (s:=col2::cols) r1.snd r2.snd

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
  inductive Subschema (bigger : Schema) : Schema → Type where
    | nil : Subschema bigger []
    | cons :
        HasCol bigger n t →
        Subschema bigger smaller →
        Subschema bigger (⟨n, t⟩ :: smaller)
stop book declaration


abbrev travelDiary : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]


book declaration {{{ peakDiarySub }}}
  example : Subschema peak travelDiary :=
    .cons .here
      (.cons (.there .here)
        (.cons (.there (.there (.there .here))) .nil))
stop book declaration


book declaration {{{ emptySub }}}
  example : Subschema peak [] := by constructor
stop book declaration


expect error {{{ notDone }}}
  example : Subschema peak [⟨"location", .string⟩] := by constructor
message
"unsolved goals
case a
⊢ HasCol peak \"location\" DBType.string

case a
⊢ Subschema peak []"
end expect


expect error {{{ notDone2 }}}
  example : Subschema peak [⟨"location", .string⟩] := by
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
⊢ Subschema peak []"
end expect


expect error {{{ notDone3 }}}
  example : Subschema peak [⟨"location", .string⟩] := by
    constructor
    constructor
    constructor
message
"unsolved goals
case a
⊢ Subschema peak []"
end expect




book declaration {{{ notDone4 }}}
  example : Subschema peak [⟨"location", .string⟩] := by
    constructor
    constructor
    constructor
    constructor
stop book declaration


book declaration {{{ notDone5 }}}
  example : Subschema peak [⟨"location", .string⟩] :=
    .cons (.there .here) .nil
stop book declaration


book declaration {{{ notDone6 }}}
  example : Subschema peak [⟨"location", .string⟩] := by repeat constructor
stop book declaration


book declaration {{{ subschemata }}}
  example : Subschema peak travelDiary := by repeat constructor

  example : Subschema waterfall travelDiary := by repeat constructor
stop book declaration

def Subschema.add (sub : Subschema bigger smaller) : Subschema (c :: bigger) smaller :=
  match sub with
  | .nil  => .nil
  | .cons col sub' => .cons (.there col) sub'.add

def Subschema.same : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (same cs).add



def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')

def Row.project (row : Row s) : (s' : Schema) → Subschema s s' → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)

inductive Cond : Schema → DBType → Type where
  | col (n : String) (loc : HasCol s n t) : Cond s t
  | eq (e1 e2 : Cond s t) : Cond s .bool
  | lt (e1 e2 : Cond s .int) : Cond s .bool
  | and (e1 e2 : Cond s .bool) : Cond s .bool
  | const : t.asType → Cond s t

def Cond.evaluate (row : Row s) : Cond s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2  => evaluate row e1 == evaluate row e2
  | .lt e1 e2  => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v

def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)

def renameSchema : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameSchema cs next n'

inductive RelAlg : Schema → Type where
  | table : Table s → RelAlg s
  | union : RelAlg s → RelAlg s → RelAlg s
  | diff : RelAlg s → RelAlg s → RelAlg s
  | select : RelAlg s → Cond s .bool → RelAlg s
  | project : RelAlg s → (s' : Schema) → Subschema s s' → RelAlg s'
  | product :
      RelAlg s1 → RelAlg s2 →
      disjoint (s1.map Column.name) (s2.map Column.name) →
      RelAlg (s1 ++ s2)
  | rename :
      RelAlg s → (c : HasCol s n t) → (n' : String) →
      RelAlg (renameSchema s c n')
  | prefixWith :
      (n : String) → RelAlg s →
      RelAlg (s.map fun c => {c with name := n ++ "." ++ c.name})

def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v =>
    match s2 with
    | [] => v
    | _::_ => (v, r2)
  | _::_::_, (v, r') => (v, append r' r2)

def List.flatMap : (xs : List α) → (f : α → List β) → List β
  | [], _ => []
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

def renameRow (row : Row s) (c : HasCol s n t) : Row (renameSchema s c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal v (renameRow r next)

def renameTable (table : Table s) (c : HasCol s n t) : Table (renameSchema s c n') :=
  table.map (renameRow · c)

def prefixRow (row : Row s) : Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)

def prefixTable (t : Table s) : Table (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  t.map prefixRow



def RelAlg.exec : RelAlg s → Table s
  | .table t => t
  | .union r1 r2 => exec r1 ++ exec r2
  | .diff r1 r2 => exec r1 |>.without (exec r2)
  | .select r e => (exec r).filter fun row => e.evaluate row
  | .project r _ sub => exec r |>.map (·.project _ sub)
  | .product r1 r2 _ => exec r1 |>.cartesianProduct (exec r2)
  | .rename r c n' => renameTable (exec r) c
  | .prefixWith n r => prefixTable (n := n) (exec r)

open RelAlg in
def example1 :=
  table mountainDiary |>.select (.lt (.const 500) (.col "elevation" (by repeat constructor))) |>.project [⟨"elevation", .int⟩] (by repeat constructor)

#eval example1.exec

open RelAlg in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfall := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfall (by simp)
    |>.select (.eq (.col "mountain.location" (by repeat constructor)) (.col "waterfall.location" (by repeat constructor)))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩] (by repeat constructor)

#eval example2.exec
