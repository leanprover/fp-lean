import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.DB"

#doc (Manual) "Worked Example: Typed Queries" =>
%%%
tag := "typed-queries"
%%%

Indexed families are very useful when building an API that is supposed to resemble some other language.
They can be used to write a library of HTML constructors that don't permit generating invalid HTML, to encode the specific rules of a configuration file format, or to model complicated business constraints.
This section describes an encoding of a subset of relational algebra in Lean using indexed families, as a simpler demonstration of techniques that can be used to build a more powerful database query language.

This subset uses the type system to enforce requirements such as disjointness of field names, and it uses type-level computation to reflect the schema into the types of values that are returned from a query.
It is not a realistic system, however—databases are represented as linked lists of linked lists, the type system is much simpler than that of SQL, and the operators of relational algebra don't really match those of SQL.
However, it is large enough to demonstrate useful principles and techniques.

# A Universe of Data
%%%
tag := "typed-query-data-universe"
%%%

In this relational algebra, the base data that can be held in columns can have types {anchorName DBType}`Int`, {anchorName DBType}`String`, and {anchorName DBType}`Bool` and are described by the universe {anchorName DBType}`DBType`:

```anchor DBType
inductive DBType where
  | int | string | bool

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
```

Using {anchorName DBType}`DBType.asType` allows these codes to be used for types.
For example:
```anchor mountHoodEval
#eval ("Mount Hood" : DBType.string.asType)
```
```anchorInfo mountHoodEval
"Mount Hood"
```

It is possible to compare the values described by any of the three database types for equality.
Explaining this to Lean, however, requires a bit of work.
Simply using {anchorName BEqDBType}`BEq` directly fails:
```anchor dbEqNoSplit
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  x == y
```
```anchorError dbEqNoSplit
failed to synthesize
  BEq t.asType

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
Just as in the nested pairs universe, type class search doesn't automatically check each possibility for {anchorName dbEqNoSplit}`t`'s value
The solution is to use pattern matching to refine the types of {anchorTerm dbEq}`x` and {anchorName dbEq}`y`:

```anchor dbEq
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
```
In this version of the function, {anchorName dbEq}`x` and {anchorName dbEq}`y` have types {anchorName DBType}`Int`, {anchorName DBType}`String`, and {anchorName DBType}`Bool` in the three respective cases, and these types all have {anchorName BEqDBType}`BEq` instances.
The definition of {anchorName dbEq}`DBType.beq` can be used to define a {anchorName BEqDBType}`BEq` instance for the types that are coded for by {anchorName DBType}`DBType`:

```anchor BEqDBType
instance {t : DBType} : BEq t.asType where
  beq := t.beq
```
This is not the same as an instance for the codes:

```anchor BEqDBTypeCodes
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
```
The former instance allows comparison of values drawn from the types described by the codes, while the latter allows comparison of the codes themselves.

A {anchorName ReprAsType}`Repr` instance can be written using the same technique.
The method of the {anchorName ReprAsType}`Repr` class is called {anchorName ReprAsType}`reprPrec` because it is designed to take things like operator precedence into account when displaying values.
Refining the type through dependent pattern matching allows the {anchorName ReprAsType}`reprPrec` methods from the {anchorName ReprAsType}`Repr` instances for {anchorName DBType}`Int`, {anchorName DBType}`String`, and {anchorName DBType}`Bool` to be used:

```anchor ReprAsType
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
```

# Schemas and Tables
%%%
tag := "schemas"
%%%

A schema describes the name and type of each column in a database:

```anchor Schema
structure Column where
  name : String
  contains : DBType

abbrev Schema := List Column
```
In fact, a schema can be seen as a universe that describes rows in a table.
The empty schema describes the unit type, a schema with a single column describes that value on its own, and a schema with at least two columns is represented by a tuple:

```anchor Row
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
```

As described in {ref "prod"}[the initial section on product types], Lean's product type and tuples are right-associative.
This means that nested pairs are equivalent to ordinary flat tuples.

A table is a list of rows that share a schema:

```anchor Table
abbrev Table (s : Schema) := List (Row s)
```
For example, a diary of visits to mountain peaks can be represented with the schema {anchorName peak}`peak`:

```anchor peak
abbrev peak : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"elevation", .int⟩,
  ⟨"lastVisited", .int⟩
]
```
A selection of peaks visited by the author of this book appears as an ordinary list of tuples:

```anchor mountainDiary
def mountainDiary : Table peak := [
  ("Mount Nebo",       "USA",     3637, 2013),
  ("Moscow Mountain",  "USA",     1519, 2015),
  ("Himmelbjerget",    "Denmark",  147, 2004),
  ("Mount St. Helens", "USA",     2549, 2010)
]
```
Another example consists of waterfalls and a diary of visits to them:

```anchor waterfall
abbrev waterfall : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"lastVisited", .int⟩
]
```

```anchor waterfallDiary
def waterfallDiary : Table waterfall := [
  ("Multnomah Falls", "USA", 2018),
  ("Shoshone Falls",  "USA", 2014)
]
```

## Recursion and Universes, Revisited
%%%
tag := "recursion-universes-revisited"
%%%

The convenient structuring of rows as tuples comes at a cost: the fact that {anchorName Row}`Row` treats its two base cases separately means that functions that use {anchorName Row}`Row` in their types and are defined recursively over the codes (that, is the schema) need to make the same distinctions.
One example of a case where this matters is an equality check that uses recursion over the schema to define a function that checks rows for equality.
This example does not pass Lean's type checker:
```anchor RowBEqRecursion
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | col::cols =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
```
```anchorError RowBEqRecursion
Type mismatch
  (v1, r1')
has type
  ?m.10 × ?m.11
but is expected to have type
  Row (col :: cols)
```
The problem is that the pattern {anchorTerm RowBEqRecursion}`col :: cols` does not sufficiently refine the type of the rows.
This is because Lean cannot yet tell whether the singleton pattern {anchorTerm Row}`[col]` or the {anchorTerm Row}`col1 :: col2 :: cols` pattern in the definition of {anchorName Row}`Row` was matched, so the call to {anchorName Row}`Row` does not compute down to a pair type.
The solution is to mirror the structure of {anchorName Row}`Row` in the definition of {anchorName RowBEq}`Row.bEq`:

```anchor RowBEq
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
```

Unlike in other contexts, functions that occur in types cannot be considered only in terms of their input/output behavior.
Programs that use these types will find themselves forced to mirror the algorithm used in the type-level function so that their structure matches the pattern-matching and recursive behavior of the type.
A big part of the skill of programming with dependent types is the selection of appropriate type-level functions with the right computational behavior.

## Column Pointers
%%%
tag := "column-pointers"
%%%

Some queries only make sense if a schema contains a particular column.
For example, a query that returns mountains with an elevation greater than 1000 meters only makes sense in the context of a schema with an {anchorTerm peak}`"elevation"` column that contains integers.
One way to indicate that a column is contained in a schema is to provide a pointer directly to it, and defining the pointer as an indexed family makes it possible to rule out invalid pointers.

There are two ways that a column can be present in a schema: either it is at the beginning of the schema, or it is somewhere later in the schema.
Eventually, if a column is later in a schema, then it will be the beginning of some tail of the schema.

The indexed family {anchorName HasCol}`HasCol` is a translation of the specification into Lean code:

```anchor HasCol
inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
```
The family's three arguments are the schema, the column name, and its type.
All three are indices, but re-ordering the arguments to place the schema after the column name and type would allow the name and type to be parameters.
The constructor {anchorName HasCol}`here` can be used when the schema begins with the column {anchorTerm HasCol}`⟨name, t⟩`; it is thus a pointer to the first column in the schema that can only be used when the first column has the desired name and type.
The constructor {anchorName HasCol}`there` transforms a pointer into a smaller schema into a pointer into a schema with one more column on it.

Because {anchorTerm peak}`"elevation"` is the third column in {anchorName peak}`peak`, it can be found by looking past the first two columns with {anchorName HasCol}`there`, after which it is the first column.
In other words, to satisfy the type {anchorTerm peakElevationInt}`HasCol peak "elevation" .int`, use the expression {anchorTerm peakElevationInt}`.there (.there .here)`.
One way to think about {anchorName HasCol}`HasCol` is as a kind of decorated {anchorName Naturals}`Nat`—{anchorName Naturals}`zero` corresponds to {anchorName HasCol}`here`, and {anchorName Naturals}`succ` corresponds to {anchorName HasCol}`there`.
The extra type information makes it impossible to have off-by-one errors.

A pointer to a particular column in a schema can be used to extract that column's value from a row:

```anchor Rowget
def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next
```
The first step is to pattern match on the schema, because this determines whether the row is a tuple or a single value.
No case is needed for the empty schema because there is a {anchorName HasCol}`HasCol` available, and both constructors of {anchorName HasCol}`HasCol` specify non-empty schemas.
If the schema has just a single column, then the pointer must point to it, so only the {anchorName HasCol}`here` constructor of {anchorName HasCol}`HasCol` need be matched.
If the schema has two or more columns, then there must be a case for {anchorName HasCol}`here`, in which case the value is the first one in the row, and one for {anchorName HasCol}`there`, in which case a recursive call is used.
Because the {anchorName HasCol}`HasCol` type guarantees that the column exists in the row, {anchorName Rowget}`Row.get` does not need to return an {anchorName nullable}`Option`.

{anchorName HasCol}`HasCol` plays two roles:
 1. It serves as _evidence_ that a column with a particular name and type exists in a schema.

 2. It serves as _data_ that can be used to find the value associated with the column in a row.

The first role, that of evidence, is similar to way that propositions are used.
The definition of the indexed family {anchorName HasCol}`HasCol` can be read as a specification of what counts as evidence that a given column exists.
Unlike propositions, however, it matters which constructor of {anchorName HasCol}`HasCol` was used.
In the second role, the constructors are used like {anchorName Naturals}`Nat`s to find data in a collection.
Programming with indexed families often requires the ability to switch fluently between both perspectives.

## Subschemas
%%%
tag := "subschemas"
%%%

One important operation in relational algebra is to _project_ a table or row into a smaller schema.
Every column not present in the smaller schema is forgotten.
In order for projection to make sense, the smaller schema must be a subschema of the larger schema, which means that every column in the smaller schema must be present in the larger schema.
Just as {anchorName HasCol}`HasCol` makes it possible to write a single-column lookup in a row that cannot fail, a representation of the subschema relationship as an indexed family makes it possible to write a projection function that cannot fail.

The ways in which one schema can be a subschema of another can be defined as an indexed family.
The basic idea is that a smaller schema is a subschema of a bigger schema if every column in the smaller schema occurs in the bigger schema.
If the smaller schema is empty, then it's certainly a subschema of the bigger schema, represented by the constructor {anchorName Subschema}`nil`.
If the smaller schema has a column, then that column must be in the bigger schema, and all the rest of the columns in the subschema must also be a subschema of the bigger schema.
This is represented by the constructor {anchorName Subschema}`cons`.

```anchor Subschema
inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger
```
In other words, {anchorName Subschema}`Subschema` assigns each column of the smaller schema a {anchorName HasCol}`HasCol` that points to its location in the larger schema.

The schema {anchorName travelDiary}`travelDiary` represents the fields that are common to both {anchorName peak}`peak` and {anchorName waterfall}`waterfall`:

```anchor travelDiary
abbrev travelDiary : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]
```
It is certainly a subschema of {anchorName peak}`peak`, as shown by this example:

```anchor peakDiarySub
example : Subschema travelDiary peak :=
  .cons .here
    (.cons (.there .here)
      (.cons (.there (.there (.there .here))) .nil))
```
However, code like this is difficult to read and difficult to maintain.
One way to improve it is to instruct Lean to write the {anchorName Subschema}`Subschema` and {anchorName HasCol}`HasCol` constructors automatically.
This can be done using the tactic feature that was introduced in {ref "props-proofs-indexing"}[the Interlude on propositions and proofs].
That interlude uses {kw}`by decide` and {kw}`by simp` to provide evidence of various propositions.

In this context, two tactics are useful:
 * The {kw}`constructor` tactic instructs Lean to solve the problem using the constructor of a datatype.
 * The {kw}`repeat` tactic instructs Lean to repeat a tactic over and over until it either fails or the proof is finished.

In the next example, {kw}`by constructor` has the same effect as just writing {anchorName peakDiarySub}`.nil` would have:

```anchor emptySub
example : Subschema [] peak := by constructor
```
However, attempting that same tactic with a slightly more complicated type fails:
```anchor notDone
example : Subschema [⟨"location", .string⟩] peak := by constructor
```
```anchorError notDone
unsolved goals
case a
⊢ HasCol peak "location" DBType.string

case a
⊢ Subschema [] peak
```
Errors that begin with {lit}`unsolved goals` describe tactics that failed to completely build the expressions that they were supposed to.
In Lean's tactic language, a _goal_ is a type that a tactic is to fulfill by constructing an appropriate expression behind the scenes.
In this case, {kw}`constructor` caused {anchorName SubschemaNames}`Subschema.cons` to be applied, and the two goals represent the two arguments expected by {anchorName Subschema}`cons`.
Adding another instance of {kw}`constructor` causes the first goal ({anchorTerm SubschemaNames}`HasCol peak "location" DBType.string`) to be addressed with {anchorName SubschemaNames}`HasCol.there`, because {anchorName peak}`peak`'s first column is not {anchorTerm SubschemaNames}`"location"`:
```anchor notDone2
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
```
```anchorError notDone2
unsolved goals
case a.a
⊢ HasCol
  [{ name := "location", contains := DBType.string }, { name := "elevation", contains := DBType.int },
    { name := "lastVisited", contains := DBType.int }]
  "location" DBType.string

case a
⊢ Subschema [] peak
```
However, adding a third {kw}`constructor` results in the first goal being solved, because {anchorName SubschemaNames}`HasCol.here` is applicable:
```anchor notDone3
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
  constructor
```
```anchorError notDone3
unsolved goals
case a
⊢ Subschema [] peak
```
A fourth instance of {kw}`constructor` solves the {anchorTerm SubschemaNames}`Subschema peak []` goal:

```anchor notDone4
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
  constructor
  constructor
```
Indeed, a version written without the use of tactics has four constructors:

```anchor notDone5
example : Subschema [⟨"location", .string⟩] peak :=
  .cons (.there .here) .nil
```

Instead of experimenting to find the right number of times to write {kw}`constructor`, the {kw}`repeat` tactic can be used to ask Lean to just keep trying {kw}`constructor` as long as it keeps making progress:

```anchor notDone6
example : Subschema [⟨"location", .string⟩] peak := by repeat constructor
```
This more flexible version also works for more interesting {anchorName Subschema}`Subschema` problems:

```anchor subschemata
example : Subschema travelDiary peak := by repeat constructor

example : Subschema travelDiary waterfall := by repeat constructor
```

The approach of blindly trying constructors until something works is not very useful for types like {anchorName Naturals}`Nat` or {anchorTerm misc}`List Bool`.
Just because an expression has type {anchorName Naturals}`Nat` doesn't mean that it's the _correct_ {anchorName Naturals}`Nat`, after all.
But types like {anchorName HasCol}`HasCol` and {anchorName Subschema}`Subschema` are sufficiently constrained by their indices that only one constructor will ever be applicable, which means that the contents of the program itself are less interesting, and a computer can pick the correct one.

If one schema is a subschema of another, then it is also a subschema of the larger schema extended with an additional column.
This fact can be captured as a function definition.
{anchorName SubschemaAdd}`Subschema.addColumn` takes evidence that {anchorName SubschemaAdd}`smaller` is a subschema of {anchorName SubschemaAdd}`bigger`, and then returns evidence that {anchorName SubschemaAdd}`smaller` is a subschema of {anchorTerm SubschemaAdd}`c :: bigger`, that is, {anchorName SubschemaAdd}`bigger` with one additional column:

```anchor SubschemaAdd
def Subschema.addColumn :
    Subschema smaller bigger →
    Subschema smaller (c :: bigger)
  | .nil  => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn
```
A subschema describes where to find each column from the smaller schema in the larger schema.
{anchorName SubschemaAdd}`Subschema.addColumn` must translate these descriptions from the original larger schema into the extended larger schema.
In the {anchorName Subschema}`nil` case, the smaller schema is {lit}`[]`, and {anchorName Subschema}`nil` is also evidence that {lit}`[]` is a subschema of {anchorTerm SubschemaAdd}`c :: bigger`.
In the {anchorName Subschema}`cons` case, which describes how to place one column from {anchorName SubschemaAdd}`smaller` into {anchorName SubschemaAdd}`bigger`, the placement of the column needs to be adjusted with {anchorName HasCol}`there` to account for the new column {anchorName SubschemaAdd}`c`, and a recursive call adjusts the rest of the columns.

Another way to think about {anchorName Subschema}`Subschema` is that it defines a _relation_ between two schemas—the existence of an expression  with type {anchorTerm misc}`Subschema smaller bigger` means that {anchorTerm misc}`(smaller, bigger)` is in the relation.
This relation is reflexive, meaning that every schema is a subschema of itself:

```anchor SubschemaSame
def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn
```


## Projecting Rows
%%%
tag := "projecting-rows"
%%%

Given evidence that {anchorName RowProj}`s'` is a subschema of {anchorName RowProj}`s`, a row in {anchorName RowProj}`s` can be projected into a row in {anchorName RowProj}`s'`.
This is done using the evidence that {anchorName RowProj}`s'` is a subschema of {anchorName RowProj}`s`, which explains where each column of {anchorName RowProj}`s'` is found in {anchorName RowProj}`s`.
The new row in {anchorName RowProj}`s'` is built up one column at a time by retrieving the value from the appropriate place in the old row.

The function that performs this projection, {anchorName RowProj}`Row.project`, has three cases, one for each case of {anchorName RowProj}`Row` itself.
It uses {anchorName Rowget}`Row.get` together with each {anchorName HasCol}`HasCol` in the {anchorName RowProj}`Subschema` argument to construct the projected row:

```anchor RowProj
def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)
```


# Conditions and Selection
%%%
tag := "conditions-and-selection"
%%%

Projection removes unwanted columns from a table, but queries must also be able to remove unwanted rows.
This operation is called _selection_.
Selection relies on having a means of expressing which rows are desired.

The example query language contains expressions, which are analogous to what can be written in a {lit}`WHERE` clause in SQL.
Expressions are represented by the indexed family {anchorName DBExpr}`DBExpr`.
Because expressions can refer to columns from the database, but different sub-expressions all have the same schema, {anchorName DBExpr}`DBExpr` takes the database schema as a parameter.
Additionally, each expression has a type, and these vary, making it an index:

```anchor DBExpr
inductive DBExpr (s : Schema) : DBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t
  | eq (e1 e2 : DBExpr s t) : DBExpr s .bool
  | lt (e1 e2 : DBExpr s .int) : DBExpr s .bool
  | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
  | const : t.asType → DBExpr s t
```
The {anchorName DBExpr}`col` constructor represents a reference to a column in the database.
The {anchorName DBExpr}`eq` constructor compares two expressions for equality, {anchorName DBExpr}`lt` checks whether one is less than the other, {anchorName DBExpr}`and` is Boolean conjunction, and {anchorName DBExpr}`const` is a constant value of some type.

For example, an expression in {anchorName peak}`peak` that checks whether the {lit}`elevation` column is greater than 1000 and the location is {anchorTerm mountainDiary}`"Denmark"` can be written:

```anchor tallDk
def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (.col "elevation" (by repeat constructor)))
       (.eq (.col "location" (by repeat constructor)) (.const "Denmark"))
```
This is somewhat noisy.
In particular, references to columns contain boilerplate calls to {anchorTerm tallDk}`by repeat constructor`.
A Lean feature called _macros_ can help make expressions easier to read by eliminating this boilerplate:

```anchor cBang
macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))
```
This declaration adds the {kw}`c!` keyword to Lean, and instructs Lean to replace any instance of {kw}`c!` followed by an expression with the corresponding {anchorTerm cBang}`DBExpr.col` construction.
Here, {anchorName cBang}`term` stands for Lean expressions, rather than commands, tactics, or some other part of the language.
Lean macros are a bit like C preprocessor macros, except they are better integrated into the language and they automatically avoid some of the pitfalls of CPP.
In fact, they are very closely related to macros in Scheme and Racket.

With this macro, the expression can be much easier to read:

```anchor tallDkBetter
def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (c! "elevation"))
       (.eq (c! "location") (.const "Denmark"))
```

Finding the value of an expression with respect to a given row uses {anchorName Rowget}`Row.get` to extract column references, and it delegates to Lean's operations on values for every other expression:

```anchor DBExprEval
def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2  => evaluate row e1 == evaluate row e2
  | .lt e1 e2  => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v
```

Evaluating the expression for Valby Bakke, the tallest hill in the Copenhagen area, yields {anchorName misc}`false` because Valby Bakke is much less than 1 km over sea level:
```anchor valbybakke
#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
```
```anchorInfo valbybakke
false
```
Evaluating it for a fictional mountain of 1230m elevation yields {anchorName misc}`true`:
```anchor fakeDkBjerg
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)
```
```anchorInfo fakeDkBjerg
true
```
Evaluating it for the highest peak in the US state of Idaho yields {anchorName misc}`false`, as Idaho is not part of Denmark:
```anchor borah
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)
```
```anchorInfo borah
false
```

# Queries
%%%
tag := "typed-query-language"
%%%

The query language is based on relational algebra.
In addition to tables, it includes the following operators:
 1. The union of two expressions that have the same schema combines the rows that result from two queries
 2. The difference of two expressions that have the same schema removes rows found in the second result from the rows in the first result
 3. Selection by some criterion filters the result of a query according to an expression
 4. Projection into a subschema, removing columns from the result of a query
 5. Cartesian product, combining every row from one query with every row from another
 6. Renaming a column in the result of a query, which modifies its schema
 7. Prefixing all columns in a query with a name

The last operator is not strictly necessary, but it makes the language more convenient to use.

Once again, queries are represented by an indexed family:

```anchor Query
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
```
The {anchorName Query}`select` constructor requires that the expression used for selection return a Boolean.
The {anchorName Query}`product` constructor's type contains a call to {anchorName Query}`disjoint`, which ensures that the two schemas don't share any names:

```anchor disjoint
def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)
```
The use of an expression of type {anchorName misc}`Bool` where a type is expected triggers a coercion from {anchorName misc}`Bool` to {anchorTerm misc}`Prop`.
Just as decidable propositions can be considered to be Booleans, where evidence for the proposition is coerced to {anchorName misc}`true` and refutations of the proposition are coerced to {anchorName misc}`false`, Booleans are coerced into the proposition that states that the expression is equal to {anchorName misc}`true`.
Because all uses of the library are expected to occur in contexts where the schemas are known ahead of time, this proposition can be proved with {kw}`by simp`.
Similarly, the {anchorName renameColumn}`renameColumn` constructor checks that the new name does not already exist in the schema.
It uses the helper {anchorName renameColumn}`Schema.renameColumn` to change the name of the column pointed to by {anchorName HasCol}`HasCol`:

```anchor renameColumn
def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'
```

# Executing Queries
%%%
tag := "executing-queries"
%%%

Executing queries requires a number of helper functions.
The result of a query is a table; this means that each operation in the query language requires a corresponding implementation that works with tables.

## Cartesian Product
%%%
tag := "executing-cartesian-product"
%%%

Taking the Cartesian product of two tables is done by appending each row from the first table to each row from the second.
First off, due to the structure of {anchorName Row}`Row`, adding a single column to a row requires pattern matching on its schema in order to determine whether the result will be a bare value or a tuple.
Because this is a common operation, factoring the pattern matching out into a helper is convenient:

```anchor addVal
def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')
```
Appending two rows is recursive on the structure of both the first schema and the first row, because the structure of the row proceeds in lock-step with the structure of the schema.
When the first row is empty, appending returns the second row.
When the first row is a singleton, the value is added to the second row.
When the first row contains multiple columns, the first column's value is added to the result of recursion on the remainder of the row.

```anchor RowAppend
def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)
```

{anchorName ListFlatMap}`List.flatMap`, found in the standard library, applies a function that itself returns a list to every entry in an input list, returning the result of appending the resulting lists in order:

```anchor ListFlatMap
def List.flatMap (f : α → List β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x ++ xs.flatMap f
```
The type signature suggests that {anchorName ListFlatMap}`List.flatMap` could be used to implement a {anchorTerm ListMonad}`Monad List` instance.
Indeed, together with {anchorTerm ListMonad}`pure x := [x]`, {anchorName ListFlatMap}`List.flatMap` does implement a monad.
However, it's not a very useful {anchorName ListMonad}`Monad` instance.
The {anchorName ListMonad}`List` monad is basically a version of {anchorName Many (module:=Examples.Monads.Many)}`Many` that explores _every_ possible path through the search space in advance, before users have the chance to request some number of values.
Because of this performance trap, it's usually not a good idea to define a {anchorName ListMonad}`Monad` instance for {anchorName ListMonad}`List`.
Here, however, the query language has no operator for restricting the number of results to be returned, so combining all possibilities is exactly what is desired:

```anchor TableCartProd
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) :=
  table1.flatMap fun r1 => table2.map r1.append
```

Just as with {anchorName ListProduct (module:=Examples.DependentTypes.Finite)}`List.product`, a loop with mutation in the identity monad can be used as an alternative implementation technique:

```anchor TableCartProdOther
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) := Id.run do
  let mut out : Table (s1 ++ s2) := []
  for r1 in table1 do
    for r2 in table2 do
      out := (r1.append r2) :: out
  pure out.reverse
```


## Difference
%%%
tag := "executing-difference"
%%%

Removing undesired rows from a table can be done using {anchorName misc}`List.filter`, which takes a list and a function that returns a {anchorName misc}`Bool`.
A new list is returned that contains only the entries for which the function returns {anchorName misc}`true`.
For instance,
```anchorTerm filterA
["Willamette", "Columbia", "Sandy", "Deschutes"].filter (·.length > 8)
```
evaluates to
```anchorTerm filterA
["Willamette", "Deschutes"]
```
because {anchorTerm filterA}`"Columbia"` and {anchorTerm filterA}`"Sandy"` have lengths less than or equal to {anchorTerm filterA}`8`.
Removing the entries of a table can be done using the helper {anchorName ListWithout}`List.without`:

```anchor ListWithout
def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)
```
This will be used with the {anchorName BEqDBType}`BEq` instance for {anchorName Row}`Row` when interpreting queries.

## Renaming Columns
%%%
tag := "executing-renaming-columns"
%%%
Renaming a column in a row is done with a recursive function that traverses the row until the column in question is found, at which point the column with the new name gets the same value as the column with the old name:

```anchor renameRow
def Row.rename (c : HasCol s n t) (row : Row s) :
    Row (s.renameColumn c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal v (r.rename next)
```
While this function changes the _type_ of its argument, the actual return value contains precisely the same data as the original argument.
From a run-time perspective, {anchorName renameRow}`Row.rename` is nothing but a slow identity function.
One difficulty in programming with indexed families is that when performance matters, this kind of operation can get in the way.
It takes a very careful, often brittle, design to eliminate these kinds of “re-indexing” functions.

## Prefixing Column Names
%%%
tag := "executing-prefixing-column-names"
%%%

Adding a prefix to column names is very similar to renaming a column.
Instead of proceeding to a desired column and then returning, {anchorName prefixRow}`prefixRow` must process all columns:

```anchor prefixRow
def prefixRow (row : Row s) :
    Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)
```
This can be used with {anchorName misc}`List.map` in order to add a prefix to all rows in a table.
Once again, this function only exists to change the type of a value.

## Putting the Pieces Together
%%%
tag := "query-exec-runner"
%%%

With all of these helpers defined, executing a query requires only a short recursive function:

```anchor QueryExec
def Query.exec : Query s → Table s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => exec q1 |>.without (exec q2)
  | .select q e => exec q |>.filter e.evaluate
  | .project q _ sub => exec q |>.map (·.project _ sub)
  | .product q1 q2 _ => exec q1 |>.cartesianProduct (exec q2)
  | .renameColumn q c _ _ => exec q |>.map (·.rename c)
  | .prefixWith _ q => exec q |>.map prefixRow
```
Some arguments to the constructors are not used during execution.
In particular, both the constructor {anchorName Query}`project` and the function {anchorName RowProj}`Row.project` take the smaller schema as explicit arguments, but the type of the _evidence_ that this schema is a subschema of the larger schema contains enough information for Lean to fill out the argument automatically.
Similarly, the fact that the two tables have disjoint column names that is required by the {anchorName Query}`product` constructor is not needed by {anchorName TableCartProd}`Table.cartesianProduct`.
Generally speaking, dependent types provide many opportunities to have Lean fill out arguments on behalf of the programmer.

Dot notation is used with the results of queries to call functions defined both in the {lit}`Table` and {lit}`List` namespaces, such {anchorName misc}`List.map`, {anchorName misc}`List.filter`, and {anchorName TableCartProd}`Table.cartesianProduct`.
This works because {anchorName Table}`Table` is defined using {kw}`abbrev`.
Just like type class search, dot notation can see through definitions created with {kw}`abbrev`.

The implementation of {anchorName Query}`select` is also quite concise.
After executing the query {anchorName selectCase}`q`, {anchorName misc}`List.filter` is used to remove the rows that do not satisfy the expression.
{anchorName misc}`List.filter` expects a function from {anchorTerm Table}`Row s` to {anchorName misc}`Bool`, but {anchorName DBExprEval}`DBExpr.evaluate` has type {anchorTerm DBExprEvalType}`Row s → DBExpr s t → t.asType`.
Because the type of the {anchorName Query}`select` constructor requires that the expression have type {anchorTerm Query}`DBExpr s .bool`, {anchorTerm DBExprEvalType}`t.asType` is actually {anchorName misc}`Bool` in this context.

A query that finds the heights of all mountain peaks with an elevation greater than 500 meters can be written:

```anchor Query1
open Query in
def example1 :=
  table mountainDiary |>.select
  (.lt (.const 500) (c! "elevation")) |>.project
  [⟨"elevation", .int⟩] (by repeat constructor)
```

Executing it returns the expected list of integers:
```anchor Query1Exec
#eval example1.exec
```
```anchorInfo Query1Exec
[3637, 1519, 2549]
```

To plan a sightseeing tour, it may be relevant to match all pairs mountains and waterfalls in the same location.
This can be done by taking the Cartesian product of both tables, selecting only the rows in which they are equal, and then projecting out the names:

```anchor Query2
open Query in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfall := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfall (by decide)
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
```
Because the example data includes only waterfalls in the USA, executing the query returns pairs of mountains and waterfalls in the US:
```anchor Query2Exec
#eval example2.exec
```
```anchorInfo Query2Exec
[("Mount Nebo", "Multnomah Falls"), ("Mount Nebo", "Shoshone Falls"), ("Moscow Mountain", "Multnomah Falls"),
  ("Moscow Mountain", "Shoshone Falls"), ("Mount St. Helens", "Multnomah Falls"),
  ("Mount St. Helens", "Shoshone Falls")]
```

## Errors You May Meet
%%%
tag := "typed-queries-error-messages"
%%%


Many potential errors are ruled out by the definition of {anchorName Query}`Query`.
For instance, forgetting the added qualifier in {anchorTerm Query2}`"mountain.location"` yields a compile-time error that highlights the column reference {anchorTerm QueryOops1}`c! "location"`:
```anchor QueryOops1
open Query in
def example2 :=
  let mountains := table mountainDiary |>.prefixWith "mountain"
  let waterfalls := table waterfallDiary |>.prefixWith "waterfall"
  mountains.product waterfalls (by simp)
    |>.select (.eq (c! "location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
```
This is excellent feedback!
On the other hand, the text of the error message is quite difficult to act on:
```anchorError QueryOops1
unsolved goals
case a.a.a.a.a.a.a
mountains : Query (List.map (fun c => { name := "mountain" ++ "." ++ c.name, contains := c.contains }) peak) := ⋯
waterfalls : Query (List.map (fun c => { name := "waterfall" ++ "." ++ c.name, contains := c.contains }) waterfall) := ⋯
⊢ HasCol (List.map (fun c => { name := "waterfall" ++ "." ++ c.name, contains := c.contains }) []) "location" ?m.62066
```

Similarly, forgetting to add prefixes to the names of the two tables results in an error on {kw}`by decide`, which should provide evidence that the schemas are in fact disjoint:
```anchor QueryOops2
open Query in
def example2 :=
  let mountains := table mountainDiary
  let waterfalls := table waterfallDiary
  mountains.product waterfalls (by decide)
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
```
This error message is more helpful:
```anchorError QueryOops2
Tactic `decide` proved that the proposition
  disjoint (List.map Column.name peak) (List.map Column.name waterfall) = true
is false
```

Lean's macro system contains everything needed not only to provide a convenient syntax for queries, but also to arrange for the error messages to be helpful.
Unfortunately, it is beyond the scope of this book to provide a description of implementing languages with Lean macros.
An indexed family such as {anchorName Query}`Query` is probably best as the core of a typed database interaction library, rather than its user interface.

# Exercises
%%%
tag := "typed-query-exercises"
%%%

## Dates
%%%
tag := none
%%%

Define a structure to represent dates. Add it to the {anchorName DBExpr}`DBType` universe and update the rest of the code accordingly. Provide the extra {anchorName DBExpr}`DBExpr` constructors that seem to be necessary.

## Nullable Types
%%%
tag := none
%%%

Add support for nullable columns to the query language by representing database types with the following structure:
```anchor nullable
structure NDBType where
  underlying : DBType
  nullable : Bool

abbrev NDBType.asType (t : NDBType) : Type :=
  if t.nullable then
    Option t.underlying.asType
  else
    t.underlying.asType
```

Use this type in place of {anchorName DBExpr}`DBType` in {anchorName Schema}`Column` and {anchorName DBExpr}`DBExpr`, and look up SQL's rules for {lit}`NULL` and comparison operators to determine the types of {anchorName DBExpr}`DBExpr`'s constructors.

## Experimenting with Tactics
%%%
tag := none
%%%


What is the result of asking Lean to find values of the following types using {kw}`by repeat constructor`? Explain why each gives the result that it does.
 * {anchorName Naturals}`Nat`
 * {anchorTerm misc}`List Nat`
 * {anchorTerm misc}`Vect Nat 4`

 * {anchorTerm misc}`Row []`
 * {anchorTerm misc}`Row [⟨"price", .int⟩]`
 * {anchorTerm misc}`Row peak`
 * {anchorTerm misc}`HasCol [⟨"price", .int⟩, ⟨"price", .int⟩] "price" .int`
