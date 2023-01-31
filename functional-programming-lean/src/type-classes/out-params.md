# Controlling Instance Search

An instance of the `Add` class is sufficient to allow two expressions with type `Pos` to be conveniently added, producing another `Pos`.
However, in many cases, it can be useful to be more flexible and allow _heterogeneous_ operator overloading, where the arguments may have different types.
For example, adding a `Nat` to a `Pos` or a `Pos` to a `Nat` will always yield a `Pos`:
```lean
{{#example_decl Examples/Classes.lean addNatPos}}
```
These functions allow natural numbers to be added to positive numbers, but they cannot be used with the `Add` type class, which expects both arguments to `add` to have the same type.

## Heterogeneous Overloadings

As mentioned in the section on [overloaded addition](pos.md#overloaded-addition), Lean provides a type class called `HAdd` for overloading addition heterogeneously.
The `HAdd` class takes three type parameters: the two argument types and the return type.
Instances of `HAdd Nat Pos Pos` and `HAdd Pos Nat Pos` allow ordinary addition notation to be used to mix the types:
```lean
{{#example_decl Examples/Classes.lean haddInsts}}
```
Given the above two instances, the following examples work:
```lean
{{#example_in Examples/Classes.lean posNatEx}}
```
```output info
{{#example_out Examples/Classes.lean posNatEx}}
```
```lean
{{#example_in Examples/Classes.lean natPosEx}}
```
```output info
{{#example_out Examples/Classes.lean natPosEx}}
```

The definition of the `HAdd` type class is very much like the following definition of `HPlus` with the corresponding instances:
```lean
{{#example_decl Examples/Classes.lean HPlus}}

{{#example_decl Examples/Classes.lean HPlusInstances}}
```
However, instances of `HPlus` are significantly less useful than instances of `HAdd`.
When attempting to use these instances with `#eval`, an error occurs:
```lean
{{#example_in Examples/Classes.lean hPlusOops}}
```
```output error
{{#example_out Examples/Classes.lean hPlusOops}}
```
This happens because there is a metavariable in the type, and Lean has no way to solve it.

As discussed in [the initial description of polymorphism](../getting-to-know/polymorphism.md), metavariables represent unknown parts of a program that could not be inferred.
When an expression is written following `#eval`, Lean attempts to determine its type automatically.
In this case, it could not.
Because the third type parameter for `HPlus` was unknown, Lean couldn't carry out type class instance search, but instance search is the only way that Lean could determine the expression's type.
That is, the `HPlus Pos Nat Pos` instance can only apply if the expression should have type `Pos`, but there's nothing in the program other than the instance itself to indicate that it should have this type.

One solution to the problem is to ensure that all three types are available by adding a type annotation to the whole expression:
```lean
{{#example_in Examples/Classes.lean hPlusLotsaTypes}}
```
```output info
{{#example_out Examples/Classes.lean hPlusLotsaTypes}}
```
However, this solution is not very convenient for users of the positive number library.


## Output Parameters

This problem can also be solved by declaring `γ` to be an _output parameter_.
Most type class parameters are inputs to the search algorithm: they are used to select an instance.
For example, in an `OfNat` instance, both the type and the natural number are used to select a particular interpretation of a natural number literal.
However, in some cases, it can be convenient to start the search process even when some of the type parameters are not yet known, and use the instances that are discovered in the search to determine values for metavariables.
The parameters that aren't needed to start instance search are outputs of the process, which is declared with the `outParam` modifier:
```lean
{{#example_decl Examples/Classes.lean HPlusOut}}
```

With this output parameter, type class instance search is able to select an instance without knowing `γ` in advance.
For instance:
```lean
{{#example_in Examples/Classes.lean hPlusWorks}}
```
```output info
{{#example_out Examples/Classes.lean hPlusWorks}}
```

It might be helpful to think of output parameters as defining a kind of function.
Any given instance of a type class that has one or more output parameters provides Lean with instructions for determining the outputs from the inputs.
The process of searching for an instance, possibly recursively, ends up being more powerful than mere overloading.
Output parameters can determine other types in the program, and instance search can assemble a collection of underlying instances into a program that has this type.

## Default Instances

Deciding whether a parameter is an input or an output controls the circumstances under which Lean will initiate type class search.
In particular, type class search does not occur until all inputs are known.
However, in some cases, output parameters are not enough, and instance search should also occur when some inputs are unknown.
This is a bit like default values for optional function arguments in Python or Kotlin, except default _types_ are being selected.

_Default instances_ are instances that are available for instance search _even when not all their inputs are known_.
When one of these instances can be used, it will be used.
This can cause programs to successfully type check, rather than failing with errors related to unknown types and metavariables.
On the other hand, default instances can make instance selection less predictable.
In particular, if an undesired default instance is selected, then an expression may have a different type than expected, which can cause confusing type errors to occur elsewhere in the program.
Be selective about where default instances are used!

One example of where default instances can be useful is an instance of `HPlus` that can be derived from an `Add` instance.
In other words, ordinary addition is a special case of heterogeneous addition in which all three types happen to be the same.
This can be implemented using the following instance:
```lean
{{#example_decl Examples/Classes.lean notDefaultAdd}}
```
With this instance, `hPlus` can be used for any addable type, like `Nat`:
```lean
{{#example_in Examples/Classes.lean hPlusNatNat}}
```
```output info
{{#example_out Examples/Classes.lean hPlusNatNat}}
```

However, this instance will only be used in situations where the types of both arguments are known.
For example,
```lean
{{#example_in Examples/Classes.lean plusFiveThree}}
```
yields the type
```output info
{{#example_out Examples/Classes.lean plusFiveThree}}
```
as expected, but
```lean
{{#example_in Examples/Classes.lean plusFiveMeta}}
```
yields a type that contains two metavariables, one for the remaining argument and one for the return type:
```output info
{{#example_out Examples/Classes.lean plusFiveMeta}}
```

In the vast majority of cases, when someone supplies one argument to addition, the other argument will have the same type.
To make this instance into a default instance, apply the `default_instance` attribute:
```lean
{{#example_decl Examples/Classes.lean defaultAdd}}
```
With this default instance, the example has a more useful type:
```lean
{{#example_in Examples/Classes.lean plusFive}}
```
yields
```output info
{{#example_out Examples/Classes.lean plusFive}}
```

Each operator that exists in overloadable heterogeneous and homogeneous versions follows the pattern of a default instance that allows the homogeneous version to be used in contexts where the heterogeneous is expected.
The infix operator is replaced with a call to the heterogeneous version, and the homogeneous default instance is selected when possible.

Similarly, simply writing `{{#example_in Examples/Classes.lean fiveType}}` gives a `{{#example_out Examples/Classes.lean fiveType}}` rather than a type with a metavariable that is waiting for more information in order to select an `OfNat` instance.
This is because the `OfNat` instance for `Nat` is a default instance.

Default instances can also be assigned _priorities_ that affect which will be chosen in situations where more than one might apply.
For more information on default instance priorities, please consult the Lean manual.


## Exercises

Define an instance of `HMul (PPoint α) α (PPoint α)` that multiplies both projections by the scalar.
It should work for any type `α` for which there is a `Mul α` instance.
For example,
```lean
{{#example_in Examples/Classes.lean HMulPPoint}}
```
should yield
```output info
{{#example_out Examples/Classes.lean HMulPPoint}}
```
