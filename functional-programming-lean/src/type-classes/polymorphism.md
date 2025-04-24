# Type Classes and Polymorphism

It can be useful to write functions that work for _any_ overloading of a given function.
For instance, `IO.println` works for any type that has an instance of `ToString`.
This is indicated using square brackets around the required instance: the type of `IO.println` is `{{#example_out Examples/Classes.lean printlnType}}`.
This type says that `IO.println` accepts an argument of type `α`, which Lean should determine automatically, and that there must be a `ToString` instance available for `α`.
It returns an `IO` action.


## Checking Polymorphic Functions' Types

Checking the type of a function that takes implicit arguments or uses type classes requires the use of some additional syntax.
Simply writing
```lean
{{#example_in Examples/Classes.lean printlnMetas}}
```
yields a type with metavariables:
```output info
{{#example_out Examples/Classes.lean printlnMetas}}
```
This is because Lean does its best to discover implicit arguments, and the presence of metavariables indicates that it did not yet discover enough type information to do so.
To understand the signature of a function, this feature can be suppressed with an at-sign (`@`) before the function's name:
```lean
{{#example_in Examples/Classes.lean printlnNoMetas}}
```
```output info
{{#example_out Examples/Classes.lean printlnNoMetas}}
```
In this output, the instance itself has been given the name `inst`.
Additionally, there is a `u_1` after `Type`, which uses a feature of Lean that has not yet been introduced.
For now, ignore these parameters to `Type`.

## Defining Polymorphic Functions with Instance Implicits

A function that sums all entries in a list needs two instances: `Add` allows the entries to be added, and an `OfNat` instance for `0` provides a sensible value to return for the empty list:
```lean
{{#example_decl Examples/Classes.lean ListSum}}
```
This function can be also defined with a `Zero α` requirement instead of `OfNat α 0`.
Both are equivalent, but `Zero α` can be easier to read:
```lean
{{#example_decl Examples/Classes.lean ListSumZ}}
```

This function can be used for a list of `Nat`s:
```lean
{{#example_decl Examples/Classes.lean fourNats}}

{{#example_in Examples/Classes.lean fourNatsSum}}
```
```output info
{{#example_out Examples/Classes.lean fourNatsSum}}
```
but not for a list of `Pos` numbers:
```lean
{{#example_decl Examples/Classes.lean fourPos}}

{{#example_in Examples/Classes.lean fourPosSum}}
```
```output error
{{#example_out Examples/Classes.lean fourPosSum}}
```
The Lean standard library includes this function, where it is called `List.sum`.

Specifications of required instances in square brackets are called _instance implicits_.
Behind the scenes, every type class defines a structure that has a field for each overloaded operation.
Instances are values of that structure type, with each field containing an implementation.
At a call site, Lean is responsible for finding an instance value to pass for each instance implicit argument.
The most important difference between ordinary implicit arguments and instance implicits is the strategy that Lean uses to find an argument value.
In the case of ordinary implicit arguments, Lean uses a technique called _unification_ to find a single unique argument value that would allow the program to pass the type checker.
This process relies only on the specific types involved in the function's definition and the call site.
For instance implicits, Lean instead consults a built-in table of instance values.

Just as the `OfNat` instance for `Pos` took a natural number `n` as an automatic implicit argument, instances may also take instance implicit arguments themselves.
The [section on polymorphism](../getting-to-know/polymorphism.md) presented a polymorphic point type:
```lean
{{#example_decl Examples/Classes.lean PPoint}}
```
Addition of points should add the underlying `x` and `y` fields.
Thus, an `Add` instance for `PPoint` requires an `Add` instance for whatever type these fields have.
In other words, the `Add` instance for `PPoint` requires a further `Add` instance for `α`:
```lean
{{#example_decl Examples/Classes.lean AddPPoint}}
```
When Lean encounters an addition of two points, it searches for and finds this instance.
It then performs a further search for the `Add α` instance.

The instance values that are constructed in this way are values of the type class's structure type.
A successful recursive instance search results in a structure value that has a reference to another structure value.
An instance of `Add (PPoint Nat)` contains a reference to the instance of `Add Nat` that was found.

This recursive search process means that type classes offer significantly more power than plain overloaded functions.
A library of polymorphic instances is a set of code building blocks that the compiler will assemble on its own, given nothing but the desired type.
Polymorphic functions that take instance arguments are latent requests to the type class mechanism to assemble helper functions behind the scenes.
The API's clients are freed from the burden of plumbing together all of the necessary parts by hand.


## Methods and Implicit Arguments


The type of `{{#example_in Examples/Classes.lean ofNatType}}` may be surprising.
It is `{{#example_out Examples/Classes.lean ofNatType}}`, in which the `Nat` argument `n` occurs as an explicit function parameter.
In the declaration of the method, however, `ofNat` simply has type `α`.
This seeming discrepancy is because declaring a type class really results in the following:

 * A structure type to contain the implementation of each overloaded operation
 * A namespace with the same name as the class
 * For each method, a function in the class's namespace that retrieves its implementation from an instance

This is analogous to the way that declaring a new structure also declares accessor functions.
The primary difference is that a structure's accessors take the structure value as an explicit parameter, while the type class methods take the instance value as an instance implicit to be found automatically by Lean.

In order for Lean to find an instance, its parameters must be available.
This means that each parameter to the type class must be a parameter to the method that occurs before the instance.
It is most convenient when these parameters are implicit, because Lean does the work of discovering their values.
For example, `{{#example_in Examples/Classes.lean addType}}` has the type `{{#example_out Examples/Classes.lean addType}}`.
In this case, the type parameter `α` can be implicit because the arguments to `Add.add` provide information about which type the user intended.
This type can then be used to search for the `Add` instance.

In the case of `ofNat`, however, the particular `Nat` literal to be decoded does not appear as part of any other parameter's type.
This means that Lean would have no information to use when attempting to figure out the implicit parameter `n`.
The result would be a very inconvenient API.
Thus, in these cases, Lean uses an explicit parameter for the class's method.



## Exercises

### Even Number Literals

Write an instance of `OfNat` for the even number datatype from the [previous section's exercises](pos.md#even-numbers) that uses recursive instance search.

### Recursive Instance Search Depth

There is a limit to how many times the Lean compiler will attempt a recursive instance search.
This places a limit on the size of even number literals defined in the previous exercise.
Experimentally determine what the limit is.
