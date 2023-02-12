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
