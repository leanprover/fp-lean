# Worked Example: Typed Queries

Indexed families are very useful when building an API that is supposed to resemble some other language.
They can be used to write a library of HTML constructors that don't permit generating invalid HTML, to encode the rules of a data format such as a `crontab` file, or to model complicated business constraints.
This section describes an encoding of a subset of relational algebra in Lean using indexed families, as a simpler demonstration of techniques that can be used to build a more powerful database query language.
This subset uses the type system to enforce requirements such as disjointness of field names, and it uses type-level computation to reflect the schema into the types of values that are returned from a query.
It is not a realistic system, however—databases are represented as linked lists of linked lists, the type system is much simpler than that of SQL, and the operators of relational algebra don't really match those of SQL.
However, it is large enough to demonstrate useful principles and techniques.

## A Universe of Data
In this relational algebra, the base data that can be held in columns can have types `Int`, `String`, and `Bool` and are described by the universe `DBType`:
```lean
{{#example_decl Examples/DependentTypes/DB.lean DBType}}
```

Using `asType` allows these codes to be used for types.
For example:
```lean
{{#example_in Examples/DependentTypes/DB.lean mountHoodEval}}
```
```output info
{{#example_out Examples/DependentTypes/DB.lean mountHoodEval}}
```

It is possible to compare the values described by any of the three database types for equality.
Explaining this to Lean, however, requires a bit of work.
Simply using `BEq` directly fails:
```lean
{{#example_in Examples/DependentTypes/DB.lean dbEqNoSplit}}
```
```output info
{{#example_out Examples/DependentTypes/DB.lean dbEqNoSplit}}
```
This is because type class search doesn't automatically check each possibility for `t`'s value.
The solution is to use pattern matching to refine the types of `x` and `y`:
```lean
{{#example_decl Examples/DependentTypes/DB.lean dbEq}}
```
In this version of the function, `x` and `y` have types `Int`, `String`, and `Bool` in the three respective cases, and these types all have `BEq` instances.
The definition of `dbEq` can be used to define a `BEq` instance for the types that are coded for by `DBType`:
```lean
{{#example_decl Examples/DependentTypes/DB.lean BEqDBType}}
```
This is not the same as an instance for the codes themselves:
```lean
{{#example_decl Examples/DependentTypes/DB.lean BEqDBTypeCodes}}
```
The former instance allows comparison of values drawn from the types described by the codes, while the latter allows comparison of the codes themselves.
 
A `Repr` instance can be written using the same technique.
The method of the `Repr` class is called `reprPrec` because it is designed to take things like operator precedence into account when displaying values.
Refining the type through pattern matching allows the `reprPrec` methods from the `Repr` instances for `Int`, `String`, and `Bool` to be used:
```lean
{{#example_decl Examples/DependentTypes/DB.lean ReprAsType}}
```


## Schemas and Tables

A schema describes the name and type of each column in a database:
```lean
{{#example_decl Examples/DependentTypes/DB.lean Schema}}
```
In fact, a schema can be seen as a universe that describes rows in a table.
The empty schema describes the unit type, a schema with a single column describes that value on its own, and a schema with at least two columns is represented by a tuple.
As described in [the initial section on product types](../getting-to-know/polymorphism.md#Prod), Lean's product type and tuples are right-associative.
This means that nested pairs are equivalent to ordinary flat tuples.

A table is a list of rows that share a schema:
```lean
{{#example_decl Examples/DependentTypes/DB.lean Table}}
```
For example, a diary of visits to mountain peaks can be represented with the schema `peak`:
```lean
{{#example_decl Examples/DependentTypes/DB.lean peak}}
```
A selection of peaks visited by the author of this book appears as an ordinary list of tuples:
```lean
{{#example_decl Examples/DependentTypes/DB.lean mountainDiary}}
```
Another example consists of waterfalls and a diary of visits to them:
```lean
{{#example_decl Examples/DependentTypes/DB.lean waterfall}}

{{#example_decl Examples/DependentTypes/DB.lean waterfallDiary}}
```

### Recursion and Universes, Revisited

The convenient structuring of rows as tuples comes at a cost: the fact that `Row` treats its two base cases separately means that functions that use `Row`s but are defined recursively over the codes (that, is the schema) need to make the same distinctions.
One example of a case where this matters is an equality check that uses recursion over the schema to define a function that checks rows for equality.
This example does not pass Lean's type checker:
```lean
{{#example_in Examples/DependentTypes/DB.lean RowBEqRecursion}}
```
```output error
{{#example_out Examples/DependentTypes/DB.lean RowBEqRecursion}}
```
The problem is that the pattern `col :: cols` does not refine the type of the rows.
This is because Lean cannot yet tell whether the singleton pattern `[col]` or the `col1 :: col2 :: cols` pattern in the definition of `Row` was matched, so the call to `Row` does not compute down to a pair type.
The solution is to mirror the structure of `Row` in the definition of `Row.bEq`:
```lean
{{#example_decl Examples/DependentTypes/DB.lean RowBEq}}
```

Functions that occur in types cannot be considered only with respect to their input/output behavior.
Programs that use these types will find themselves forced to mirror the algorithm used in the type-level function so that their structure matches the pattern-matching and recursive behavior of the type.
A big part of the skill of programming with dependent types is the selection of appropriate type-level functions with the right computational behavior.

### Column Pointers

Some queries only make sense if a schema contains a particular column.
For example, a query that returns mountains with an elevation greater than 1000 meters only makes sense in the context of a schema with a `"elevation"` column that contains integers.
One way to indicate that a column is contained in a schema is to provide a pointer directly to it, and defining the pointer as an indexed family makes it possible to rule out invalid pointers.

There are two ways that a column can be present in a schema: either it is at the beginning of the schema, or it is somewhere later in the schema.
Eventually, if a column is later in a schema, then it will be the beginning of some tail of the schema.

The indexed family `HasCol` is a translation of the specification into Lean code:
```lean
{{#example_decl Examples/DependentTypes/DB.lean HasCol}}
```
The family's three arguments are the schema, the column name, and its type.
The constructor `here` can be used when the schema begins with the column `⟨name, t⟩`; it is thus a pointer to the first column in the schema that can only be used when the first column has the desired name and type.
The constructor `there` transforms a pointer into a smaller schema into a pointer into a schema with one more column on it.

Because `"elevation"` is the third column in `peak`, it can be found by looking past the first two columns with `there`, after which it is the first column.
In other words, something with type `{{#example_out Examples/DependentTypes/DB.lean peakElevationInt}}` can be built using `{{#example_in Examples/DependentTypes/DB.lean peakElevationInt}}`.
One way to think about `HasCol` is as a kind of decorated `Nat`—`zero` corresponds to `here`, and `succ` corresponds to `there`.
The extra type information makes it impossible to have off-by-one errors.

A pointer to a particular column in a schema can be used to extract that column's value from a row:
```lean
{{#example_decl Examples/DependentTypes/DB.lean Rowget}}
```
The first step is to pattern match on the schema, because this determines whether the row is a tuple or a single value.
No case is needed for the empty schema because there is a `HasCol` available, and both constructors of `HasCol` specify non-empty schemas.
If the schema has just a single column, then the pointer must point to it, so only the `here` constructor of `HasCol` need be matched.
If the schema has two or more columns, then there must be a case for `here`, in which case the value is the first one in the row, and one for `there`, in which case a recursive call is used.
Because the `HasCol` type guarantees that the column exists in the row, `Row.get` does not need to return an `Option`.

`HasCol` plays two roles:
 1. It serves as _evidence_ that a column with a particular name and type exists in a schema.

 2. It serves as _data_ that can be used to find the value associated with the column in a row.

The first role, that of evidence, is similar to way that propositions are used.
The definition of the indexed family `HasCol` can be read as a specification of what counts as evidence that a given column exists.
Unlike propositions, however, it matters which constructor of `HasCol` was used.
In the second role, the constructors are used like `Nat`s to find data in a collection.
Programming with indexed families often requires the ability to switch fluently between both perspectives.

### Subschemas

One important operation in relational algebra is to _project_ a table or row into a smaller schema.
Every column not present in the smaller schema is forgotten.
In order for projection to make sense, the smaller schema must be a subschema of the larger schema, which means that every column in the smaller schema must be present in the larger schema.
Just as `HasCol` makes it possible to write a single-column lookup in a row that cannot fail, a representation of the subschema relationship as an indexed family makes it possible to write a projection function that cannot fail.

Being a subschema can be defined as an indexed family.
The basic idea is that a smaller schema is a subschema of a bigger schema if every column in the smaller schema occurs in the bigger schema.
If the smaller schema is empty, then it's certainly a subschema of the bigger schema, represented by the constructor `nil`.
If the smaller schema has a column, then that column must be in the bigger schema, and all the rest of the columns in the subschema must also be a subschema of the bigger schema.
This is represented by the constructor `cons`.
```lean
{{#example_decl Examples/DependentTypes/DB.lean Subschema}}
```

The schema `travelDiary` represents the fields that are common to both `peak` and `waterfall`.
It is certainly a subschema of `peak`, as shown by this example:
```lean
{{#example_decl Examples/DependentTypes/DB.lean peakDiarySub}}
```
However, code like this is difficult to read and difficult to maintain.
One way to improve it is to instruct Lean to write the `Subschema` and `HasCol` constructors automatically.
This can be done using the tactic feature that was introduced in [the Interlude on propositions and proofs](../props-proofs-indexing.md).
That interlude uses `by simp` to provide evidence of various propositions.

In this context, two tactics are useful:
 * The `constructor` tactic instructs Lean to solve the problem using the constructor of a datatype.
 * The `repeat` tactic instructs Lean to repeat a tactic over and over until it either fails or the proof is finished.
In the next example, `by constructor` has the same effect as just writing `.nil` would have:
```lean
{{#example_decl Examples/DependentTypes/DB.lean emptySub}}
```
However, attempting that same tactic a slightly more complicated type fails:
```lean
{{#example_in Examples/DependentTypes/DB.lean notDone}}
```
```output error
{{#example_out Examples/DependentTypes/DB.lean notDone}}
```
Errors that begin with `unsolved goals` describe tactics that failed to completely build the expressions that they were supposed to.
In this case, `constructor` caused `Subschema.cons` to be applied, and the two goals represent the two arguments expected by `cons`.
Adding another instance of `constructor` causes the first goal (`HasCol peak \"location\" DBType.string`) to be addressed with `HasCol.there`, because `peak`'s first column is not `"location"`:
```lean
{{#example_in Examples/DependentTypes/DB.lean notDone2}}
```
```output error
{{#example_out Examples/DependentTypes/DB.lean notDone2}}
```
However, adding a third `constructor` results in the first goal being solved, because `HasCol.here` is applicable:
```lean
{{#example_in Examples/DependentTypes/DB.lean notDone3}}
```
```output error
{{#example_out Examples/DependentTypes/DB.lean notDone3}}
```
A fourth instance of `constructor` solves the `Subschema peak []` goal:
```lean
{{#example_decl Examples/DependentTypes/DB.lean notDone4}}
```
Indeed, a version written without the use of tactics has four constructors:
```lean
{{#example_decl Examples/DependentTypes/DB.lean notDone5}}
```

Instead of experimenting to find the right number of times to write `constructor`, the `repeat` tactic can be used to ask Lean to just keep trying `constructor` as long as it keeps making progress:
```lean
{{#example_decl Examples/DependentTypes/DB.lean notDone6}}
```
This more flexible version also works for more interesting `Subschema` problems:
```lean
{{#example_decl Examples/DependentTypes/DB.lean subschemata}}
```

The approach of blindly trying constructors until something works is not very useful for types like `Nat` or `List Bool`.
Just because an expression has type `Nat` doesn't mean that it's the _correct_ `Nat`, after all!
But types like `HasCol` and `Subschema` are sufficiently constrained by their indices that only one constructor will ever be applicable, which means that the contents of the program itself are fundamentally uninteresting and can be suppressed.


### Projecting Rows

## Conditions and Selection

## Queries

## Executing Queries
