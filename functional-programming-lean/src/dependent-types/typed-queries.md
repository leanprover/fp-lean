# Worked Example: Typed Queries

Indexed families are very useful when building an API that is supposed to resemble some other language.
They can be used to write a library of HTML constructors that don't permit generating invalid HTML, to encode the specific rules of a configuration file format, or to model complicated business constraints.
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
Just as in the nested pairs universe, type class search doesn't automatically check each possibility for `t`'s value
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
Refining the type through dependent pattern matching allows the `reprPrec` methods from the `Repr` instances for `Int`, `String`, and `Bool` to be used:
```lean
{{#example_decl Examples/DependentTypes/DB.lean ReprAsType}}
```

## Schemas and Tables

A schema describes the name and type of each column in a database:
```lean
{{#example_decl Examples/DependentTypes/DB.lean Schema}}
```
In fact, a schema can be seen as a universe that describes rows in a table.
The empty schema describes the unit type, a schema with a single column describes that value on its own, and a schema with at least two columns is represented by a tuple:
```lean
{{#example_decl Examples/DependentTypes/DB.lean Row}}
```

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

The convenient structuring of rows as tuples comes at a cost: the fact that `Row` treats its two base cases separately means that functions that use `Row` in their types and are defined recursively over the codes (that, is the schema) need to make the same distinctions.
One example of a case where this matters is an equality check that uses recursion over the schema to define a function that checks rows for equality.
This example does not pass Lean's type checker:
```lean
{{#example_in Examples/DependentTypes/DB.lean RowBEqRecursion}}
```
```output error
{{#example_out Examples/DependentTypes/DB.lean RowBEqRecursion}}
```
The problem is that the pattern `col :: cols` does not sufficiently refine the type of the rows.
This is because Lean cannot yet tell whether the singleton pattern `[col]` or the `col1 :: col2 :: cols` pattern in the definition of `Row` was matched, so the call to `Row` does not compute down to a pair type.
The solution is to mirror the structure of `Row` in the definition of `Row.bEq`:
```lean
{{#example_decl Examples/DependentTypes/DB.lean RowBEq}}
```

Unlike in other contexts, functions that occur in types cannot be considered only in terms of their input/output behavior.
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
All three are indices, but re-ordering the arguments to place the schema after the column name and type would allow the name and type to be parameters.
The constructor `here` can be used when the schema begins with the column `⟨name, t⟩`; it is thus a pointer to the first column in the schema that can only be used when the first column has the desired name and type.
The constructor `there` transforms a pointer into a smaller schema into a pointer into a schema with one more column on it.

Because `"elevation"` is the third column in `peak`, it can be found by looking past the first two columns with `there`, after which it is the first column.
In other words, to satisfy the type `{{#example_out Examples/DependentTypes/DB.lean peakElevationInt}}`, use the expression `{{#example_in Examples/DependentTypes/DB.lean peakElevationInt}}`.
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

The ways in which one schema can be a subschema of another can be defined as an indexed family.
The basic idea is that a smaller schema is a subschema of a bigger schema if every column in the smaller schema occurs in the bigger schema.
If the smaller schema is empty, then it's certainly a subschema of the bigger schema, represented by the constructor `nil`.
If the smaller schema has a column, then that column must be in the bigger schema, and all the rest of the columns in the subschema must also be a subschema of the bigger schema.
This is represented by the constructor `cons`.
```lean
{{#example_decl Examples/DependentTypes/DB.lean Subschema}}
```
In other words, `Subschema` assigns each column of the smaller schema a `HasCol` that points to its location in the larger schema.

The schema `travelDiary` represents the fields that are common to both `peak` and `waterfall`:
```lean
{{#example_decl Examples/DependentTypes/DB.lean travelDiary}}
```
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
```leantac
{{#example_decl Examples/DependentTypes/DB.lean emptySub}}
```
However, attempting that same tactic with a slightly more complicated type fails:
```leantac
{{#example_in Examples/DependentTypes/DB.lean notDone}}
```
```output error
{{#example_out Examples/DependentTypes/DB.lean notDone}}
```
Errors that begin with `unsolved goals` describe tactics that failed to completely build the expressions that they were supposed to.
In Lean's tactic language, a _goal_ is a type that a tactic is to fulfill by constructing an appropriate expression behind the scenes.
In this case, `constructor` caused `Subschema.cons` to be applied, and the two goals represent the two arguments expected by `cons`.
Adding another instance of `constructor` causes the first goal (`HasCol peak \"location\" DBType.string`) to be addressed with `HasCol.there`, because `peak`'s first column is not `"location"`:
```leantac
{{#example_in Examples/DependentTypes/DB.lean notDone2}}
```
```output error
{{#example_out Examples/DependentTypes/DB.lean notDone2}}
```
However, adding a third `constructor` results in the first goal being solved, because `HasCol.here` is applicable:
```leantac
{{#example_in Examples/DependentTypes/DB.lean notDone3}}
```
```output error
{{#example_out Examples/DependentTypes/DB.lean notDone3}}
```
A fourth instance of `constructor` solves the `Subschema peak []` goal:
```leantac
{{#example_decl Examples/DependentTypes/DB.lean notDone4}}
```
Indeed, a version written without the use of tactics has four constructors:
```lean
{{#example_decl Examples/DependentTypes/DB.lean notDone5}}
```

Instead of experimenting to find the right number of times to write `constructor`, the `repeat` tactic can be used to ask Lean to just keep trying `constructor` as long as it keeps making progress:
```leantac
{{#example_decl Examples/DependentTypes/DB.lean notDone6}}
```
This more flexible version also works for more interesting `Subschema` problems:
```leantac
{{#example_decl Examples/DependentTypes/DB.lean subschemata}}
```

The approach of blindly trying constructors until something works is not very useful for types like `Nat` or `List Bool`.
Just because an expression has type `Nat` doesn't mean that it's the _correct_ `Nat`, after all.
But types like `HasCol` and `Subschema` are sufficiently constrained by their indices that only one constructor will ever be applicable, which means that the contents of the program itself are less interesting, and a computer can pick the correct one.

If one schema is a subschema of another, then it is also a subschema of the larger schema extended with an additional column.
This fact can be captured as a function definition.
`Subschema.addColumn` takes evidence that `smaller` is a subschema of `bigger`, and then returns evidence that `smaller` is a subschema of `c :: bigger`, that is, `bigger` with one additional column:
```lean
{{#example_decl Examples/DependentTypes/DB.lean SubschemaAdd}}
```
A subschema describes where to find each column from the smaller schema in the larger schema.
`Subschema.addColumn` must translate these descriptions from the original larger schema into the extended larger schema.
In the `nil` case, the smaller schema is `[]`, and `nil` is also evidence that `[]` is a subschema of `c :: bigger`.
In the `cons` case, which describes how to place one column from `smaller` into `larger`, the placement of the column needs to be adjusted with `there` to account for the new column `c`, and a recursive call adjusts the rest of the columns.

Another way to think about `Subschema` is that it defines a _relation_ between two schemas—the existence of an expression  with type `Subschema bigger smaller` means that `(bigger, smaller)` is in the relation.
This relation is reflexive, meaning that every schema is a subschema of itself:
```lean
{{#example_decl Examples/DependentTypes/DB.lean SubschemaSame}}
```


### Projecting Rows

Given evidence that `s'` is a subschema of `s`, a row in `s` can be projected into a row in `s'`.
This is done using the evidence that `s'` is a subschema of `s`, which explains where each column of `s'` is found in `s`.
The new row in `s'` is built up one column at a time by retrieving the value from the appropriate place in the old row.

The function that performs this projection, `Row.project`, has three cases, one for each case of `Row` itself.
It uses `Row.get` together with each `HasCol` in the `Subschema` argument to construct the projected row:
```lean
{{#example_decl Examples/DependentTypes/DB.lean RowProj}}
```


## Conditions and Selection

Projection removes unwanted columns from a table, but queries must also be able to remove unwanted rows.
This operation is called _selection_.
Selection relies on having a means of expressing which rows are desired.

The example query language contains expressions, which are analogous to what can be written in a `WHERE` clause in SQL.
Expressions are represented by the indexed family `DBExpr`.
Because expressions can refer to columns from the database, but different sub-expressions all have the same schema, `DBExpr` takes the database schema as a parameter.
Additionally, each expression has a type, and these vary, making it an index:
```lean
{{#example_decl Examples/DependentTypes/DB.lean DBExpr}}
```
The `col` constructor represents a reference to a column in the database.
The `eq` constructor compares two expressions for equality, `lt` checks whether one is less than the other, `and` is Boolean conjunction, and `const` is a constant value of some type.

For example, an expression in `peak` that checks whether the `elevation` column is greater than 1000 and the location is `"Denmark"` can be written:
```leantac
{{#example_decl Examples/DependentTypes/DB.lean tallDk}}
```
This is somewhat noisy.
In particular, references to columns contain boilerplate calls to `by repeat constructor`.
A Lean feature called _macros_ can help make expressions easier to read by eliminating this boilerplate:
```leantac
{{#example_decl Examples/DependentTypes/DB.lean cBang}}
```
This declaration adds the `c!` keyword to Lean, and instructs Lean to replace any instance of `c!` followed by an expression with the corresponding `DBExpr.col` construction.
Here, `term` stands for Lean expressions, rather than commands, tactics, or some other part of the language.
Lean macros are a bit like C preprocessor macros, except they are better integrated into the language and they automatically avoid some of the pitfalls of CPP.
In fact, they are very closely related to macros in Scheme and Racket.

With this macro, the expression can be much easier to read:
```lean
{{#example_decl Examples/DependentTypes/DB.lean tallDkBetter}}
```

Finding the value of an expression with respect to a given row uses `Row.get` to extract column references, and it delegates to Lean's operations on values for every other expression:
```lean
{{#example_decl Examples/DependentTypes/DB.lean DBExprEval}}
```

Evaluating the expression for Valby Bakke, the tallest hill in the Copenhagen area, yields `false` because Valby Bakke is much less than 1 km over sea level:
```lean
{{#example_in Examples/DependentTypes/DB.lean valbybakke}}
```
```output info
{{#example_out Examples/DependentTypes/DB.lean valbybakke}}
```
Evaluating it for a fictional mountain of 1230m elevation yields `true`:
```lean
{{#example_in Examples/DependentTypes/DB.lean fakeDkBjerg}}
```
```output info
{{#example_out Examples/DependentTypes/DB.lean fakeDkBjerg}}
```
Evaluating it for the highest peak in the US state of Idaho yields `false`, as Idaho is not part of Denmark:
```lean
{{#example_in Examples/DependentTypes/DB.lean borah}}
```
```output info
{{#example_out Examples/DependentTypes/DB.lean borah}}
```

## Queries

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
```lean
{{#example_decl Examples/DependentTypes/DB.lean Query}}
```
The `select` constructor requires that the expression used for selection return a Boolean.
The `product` constructor's type contains a call to `disjoint`, which ensures that the two schemas don't share any names:
```lean
{{#example_decl Examples/DependentTypes/DB.lean disjoint}}
```
The use of an expression of type `Bool` where a type is expected triggers a coercion from `Bool` to `Prop`.
Just as decidable propositions can be considered to be Booleans, where evidence for the proposition is coerced to `true` and refutations of the proposition are coerced to `false`, Booleans are coerced into the proposition that states that the expression is equal to `true`.
Because all uses of the library are expected to occur in contexts where the schemas are known ahead of time, this proposition can be proved with `by simp`.
Similarly, the `renameColumn` constructor checks that the new name does not already exist in the schema.
It uses the helper `Schema.renameColumn` to change the name of the column pointed to by `HasCol`:
```lean
{{#example_decl Examples/DependentTypes/DB.lean renameColumn}}
```

## Executing Queries

Executing queries requires a number of helper functions.
The result of a query is a table; this means that each operation in the query language requires a corresponding implementation that works with tables.

### Cartesian Product

Taking the Cartesian product of two tables is done by appending each row from the first table to each row from the second.
First off, due to the structure of `Row`, adding a single column to a row requires pattern matching on its schema in order to determine whether the result will be a bare value or a tuple.
Because this is a common operation, factoring the pattern matching out into a helper is convenient:
```lean
{{#example_decl Examples/DependentTypes/DB.lean addVal}}
```
Appending two rows is recursive on the structure of both the first schema and the first row, because the structure of the row proceeds in lock-step with the structure of the schema.
When the first row is empty, appending returns the second row.
When the first row is a singleton, the value is added to the second row.
When the first row contains multiple columns, the first column's value is added to the result of recursion on the remainder of the row.
```lean
{{#example_decl Examples/DependentTypes/DB.lean RowAppend}}
```

`List.flatMap` applies a function that itself returns a list to every entry in an input list, returning the result of appending the resulting lists in order:
```lean
{{#example_decl Examples/DependentTypes/DB.lean ListFlatMap}}
```
The type signature suggests that `List.flatMap` could be used to implement a `Monad List` instance.
Indeed, together with `pure x := [x]`, `List.flatMap` does implement a monad.
However, it's not a very useful `Monad` instance.
The `List` monad is basically a version of `Many` that explores _every_ possible path through the search space in advance, before users have the chance to request some number of values.
Because of this performance trap, it's usually not a good idea to define a `Monad` instance for `List`.
Here, however, the query language has no operator for restricting the number of results to be returned, so combining all possibilities is exactly what is desired:
```lean
{{#example_decl Examples/DependentTypes/DB.lean TableCartProd}}
```

Just as with `List.product`, a loop with mutation in the identity monad can be used as an alternative implementation technique:
```lean
{{#example_decl Examples/DependentTypes/DB.lean TableCartProdOther}}
```


### Difference

Removing undesired rows from a table can be done using `List.filter`, which takes a list and a function that returns a `Bool`.
A new list is returned that contains only the entries for which the function returns `true`.
For instance,
```lean
{{#example_in Examples/DependentTypes/DB.lean filterA}}
```
evaluates to
```lean
{{#example_out Examples/DependentTypes/DB.lean filterA}}
```
because `"Columbia"` and `"Sandy"` have lengths less than or equal to `8`.
Removing the entries of a table can be done using the helper `List.without`:
```lean
{{#example_decl Examples/DependentTypes/DB.lean ListWithout}}
```
This will be used with the `BEq` instance for `Row` when interpreting queries.

### Renaming Columns
Renaming a column in a row is done with a recursive function that traverses the row until the column in question is found, at which point the column with the new name gets the same value as the column with the old name:
```lean
{{#example_decl Examples/DependentTypes/DB.lean renameRow}}
```
While this function changes the _type_ of its argument, the actual return value contains precisely the same data as the original argument.
From a run-time perspective, `renameRow` is nothing but a slow identity function.
One difficulty in programming with indexed families is that when performance matters, this kind of operation can get in the way.
It takes a very careful, often brittle, design to eliminate these kinds of "re-indexing" functions.

### Prefixing Column Names

Adding a prefix to column names is very similar to renaming a column.
Instead of proceeding to a desired column and then returning, `prefixRow` must process all columns:
```lean
{{#example_decl Examples/DependentTypes/DB.lean prefixRow}}
```
This can be used with `List.map` in order to add a prefix to all rows in a table.
Once again, this function only exists to change the type of a value.

### Putting the Pieces Together

With all of these helpers defined, executing a query requires only a short recursive function:
```lean
{{#example_decl Examples/DependentTypes/DB.lean QueryExec}}
```
Some arguments to the constructors are not used during execution.
In particular, both the constructor `project` and the function `Row.project` take the smaller schema as explicit arguments, but the type of the _evidence_ that this schema is a subschema of the larger schema contains enough information for Lean to fill out the argument automatically.
Similarly, the fact that the two tables have disjoint column names that is required by the `product` constructor is not needed by `Table.cartesianProduct`.
Generally speaking, dependent types provide many opportunities to have Lean fill out arguments on behalf of the programmer.

Dot notation is used with the results of queries to call functions defined both in the `Table` and `List` namespaces, such `List.map`, `List.filter`, and `Table.cartesianProduct`.
This works because `Table` is defined using `abbrev`.
Just like type class search, dot notation can see through definitions created with `abbrev`. 

The implementation of `select` is also quite concise.
After executing the query `q`, `List.filter` is used to remove the rows that do not satisfy the expression.
Filter expects a function from `Row s` to `Bool`, but `DBExpr.evaluate` has type `Row s → DBExpr s t → t.asType`.
Because the type of the `select` constructor requires that the expression have type `DBExpr s .bool`, `t.asType` is actually `Bool` in this context.

A query that finds the heights of all mountain peaks with an elevation greater than 500 meters can be written:
```leantac
{{#example_decl Examples/DependentTypes/DB.lean Query1}}
```

Executing it returns the expected list of integers:
```lean
{{#example_in Examples/DependentTypes/DB.lean Query1Exec}}
```
```output info
{{#example_out Examples/DependentTypes/DB.lean Query1Exec}}
```

To plan a sightseeing tour, it may be relevant to match all pairs mountains and waterfalls in the same location.
This can be done by taking the Cartesian product of both tables, selecting only the rows in which they are equal, and then projecting out the names:
```leantac
{{#example_decl Examples/DependentTypes/DB.lean Query2}}
```
Because the example data includes only waterfalls in the USA, executing the query returns pairs of mountains and waterfalls in the US:
```lean
{{#example_in Examples/DependentTypes/DB.lean Query2Exec}}
```
```output info
{{#example_out Examples/DependentTypes/DB.lean Query2Exec}}
```

### Errors You May Meet

Many potential errors are ruled out by the definition of `Query`.
For instance, forgetting the added qualifier in `"mountain.location"` yields a compile-time error that highlights the column reference `c! "location"`:
```leantac
{{#example_in Examples/DependentTypes/DB.lean QueryOops1}}
```
This is excellent feedback!
On the other hand, the text of the error message is quite difficult to act on:
```output error
{{#example_out Examples/DependentTypes/DB.lean QueryOops1}}
```

Similarly, forgetting to add prefixes to the names of the two tables results in an error on `by simp`, which should provide evidence that the schemas are in fact disjoint;
```leantac
{{#example_in Examples/DependentTypes/DB.lean QueryOops2}}
```
However, the error message is similarly unhelpful:
```output error
{{#example_out Examples/DependentTypes/DB.lean QueryOops2}}
```

Lean's macro system contains everything needed not only to provide a convenient syntax for queries, but also to arrange for the error messages to be helpful.
Unfortunately, it is beyond the scope of this book to provide a description of implementing languages with Lean macros.
An indexed family such as `Query` is probably best as the core of a typed database interaction library, rather than its user interface.

## Exercises

### Dates

Define a structure to represent dates. Add it to the `DBType` universe and update the rest of the code accordingly. Provide the extra `DBExpr` constructors that seem to be necessary.

### Nullable Types

Add support for nullable columns to the query language by representing database types with the following structure:
```lean
structure NDBType where
  underlying : DBType
  nullable : Bool

abbrev NDBType.asType (t : NDBType) : Type :=
  if t.nullable then
    Option t.underlying.asType
  else
    t.underlying.asType
```

Use this type in place of `DBType` in `Column` and `DBExpr`, and look up SQL's rules for `NULL` and comparison operators to determine the types of `DBExpr`'s constructors.

### Experimenting with Tactics

What is the result of asking Lean to find values of the following types using `by repeat constructor`? Explain why each gives the result that it does.
 * `Nat`
 * `List Nat`
 * `Vect Nat 4`
 * `Row []`
 * `Row [⟨"price", .int⟩]`
 * `Row peak`
 * `HasCol [⟨"price", .int⟩, ⟨"price", .int⟩] "price" .int`
