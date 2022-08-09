# Output Parameters

An instance of the `Add` class is sufficient to allow two expressions with type `Pos` to be conveniently added, producing another `Pos`.
However, in many cases, it can be useful to be more flexible and allow _heterogeneous_ operator overloading, where the arguments may have different types.
For example, adding a `Nat` to a `Pos` or a `Pos` to a `Nat` will always yield a `Pos`:
```Lean
{{#example_decl Examples/Classes.lean addNatPos}}
```
These functions allow natural numbers to be added to positive numbers, but they cannot be used with the `Add` type class, which expects both arguments to `add` to have the same type.

Handily, Lean provides a type class called `HAdd` for overloading addition heterogeneously.
The `HAdd` class takes three type parameters: the two argument types and the return type.
Instances of `HAdd Nat Pos Pos` and `HAdd Pos Nat Pos` allow ordinary addition notation to be used to mix the types:
```Lean
{{#example_decl Examples/Classes.lean haddInsts}}
```
For instance, given the above two instances, the following examples work:
```Lean
{{#example_in Examples/Classes.lean posNatEx}}
```
```Lean info
{{#example_out Examples/Classes.lean posNatEx}}
```
```Lean
{{#example_in Examples/Classes.lean natPosEx}}
```
```Lean info
{{#example_out Examples/Classes.lean natPosEx}}
```

The definition of the `HAdd` type class is very much like the following definition of `HPlus`:
```Lean
{{#example_decl Examples/Classes.lean HPlus}}
```
However, instances of `HPlus` are significantly less useful than instances of `HAdd`.
When attempting to use these instances with `#eval`, an error occurs:
```Lean
{{#example_in Examples/Classes.lean hPlusOops}}
```
```Lean error
{{#example_out Examples/Classes.lean hPlusOops}}
```
This happens because there is a metavariable in the type, and Lean has no way to solve it.

As discussed in [the initial description of polymorphism](../getting-to-know/polymorphism.md), metavariables represent unknown parts of a program that could not be inferred.
When an expression is written following `#eval`, Lean attempts to determine its type automatically.
In this case, it could not.
Because the third type parameter for `HPlus` was unknown, Lean couldn't carry out type class instance search, but instance search is the only way that Lean could determine the expression's type.
That is, the `HPlus Pos Nat Pos` instance can only apply if the expression should have type `Pos`, but there's nothing in the program other than the instance itself to indicate that it should have this type.

This problem can be solved by declaring `γ` to be an _output parameter_.
Most type class parameters are inputs to the search algorithm: they are used to select an instance.
For example, in an `OfNat` instance, both the type and the natural number are used to select a particular interpretation of a natural number literal.
However, in some cases, it can be convenient to start the search process even when some of the type parameters are not yet known, and use the instances that are discovered can be used to solve metavariables.


Sometimes, classes like `Add` are not suffic

 - HAdd, etc
 - HAppend
 - GetElem
 
 

Also show that 
