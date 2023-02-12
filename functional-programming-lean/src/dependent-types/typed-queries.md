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
The problem is that the pattern `col::cols` does not refine the type of the rows.
This is because Lean cannot yet tell whether the singleton pattern `[col]` or the `col1 :: col2 :: cols` pattern was matched, so the call to `Row` does not compute down to a pair type.
The solution is to mirror the structure of `Row` in the definition of `Row.bEq`:
```lean
{{#example_decl Examples/DependentTypes/DB.lean RowBEq}}
```

Functions that occur in types cannot be considered only with respect to their input/output behavior.
Programs that use these types will find themselves forced to mirror the algorithm used in the type-level function so that their structure matches the pattern-matching and recursive behavior of the type.
A big part of the skill of programming with dependent types is the selection of appropriate type-level functions with the right computational behavior.
