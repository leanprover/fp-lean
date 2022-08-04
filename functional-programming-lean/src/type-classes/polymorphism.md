# Type Classes and Polymorphism

It can be useful to write functions that work for _any_ overloading of a given function.
For instance, `IO.println` works for any type that has an instance of `ToString`.
This is indicated using square brackets around the required instance: the type of `IO.println` is `{{#example_out Examples/Classes.lean printlnType}}`.
This type says that `IO.println` accepts an argument of type `α`, which Lean should determine automatically, and that there must be a `ToString` instance available for `α`.
It returns an `IO` action.

Similarly, a function that sums all entries in a list needs two instances: `Add` allows the entries to be added, and an `OfNat` instance for `0` provides a sensible value to return for the empty list:
```Lean
{{#example_decl Examples/Classes.lean ListSum}}
```
This function can be used for a list of `Nat`s:
```Lean
{{#example_decl Examples/Classes.lean fourNats}}

{{#example_in Examples/Classes.lean fourNatsSum}}
```
```Lean info
{{#example_out Examples/Classes.lean fourNatsSum}}
```
but not for a list of `Pos` numbers:
```Lean
{{#example_decl Examples/Classes.lean fourPos}}

{{#example_in Examples/Classes.lean fourPosSum}}
```
```Lean error
{{#example_out Examples/Classes.lean fourPosSum}}
```

Specifications of required instances in square brackets are called _instance implicits_.
Behind the scenes, every type class defines a structure that has a field for each overloaded operation.
Instances are values of that structure type, with each field containing an implementation.
At a call site, Lean is responsible for finding an instance value to pass for each instance implicit argument.
The most important difference between ordinary implicit arguments and instance implicits is the strategy that Lean uses to find an argument value.
In the case of ordinary implicit arguments, Lean uses a technique called _unification_ to find a single unique argument value that would allow the program to pass the type checker.
This process relies only on the specific types involved in the function's definition and the call site.
For instance implicits, Lean instead consults a built-in table of instance values.

Instances may themselves take instance implicit arguments.
The [section on polymorphism](../getting-to-know/polymorphism.md) presented a polymorphic point type:
```Lean
{{#example_decl Examples/Classes.lean PPoint}}
```
Addition of points should add the underlying `x` and `y` fields.
Thus, an `Add` instance for `PPoint` requires an `Add` instance for whatever type these fields have.
In other words, the `Add` instance for `PPoint` requires a further `Add` instance:
```Lean
{{#example_decl Examples/Classes.lean AddPPoint}}
```
When Lean encounters an addition of two points, it searches for and finds this instance.
It then performs a further search for the `Add α` instance.

This recursive search process means that type classes offer significantly more power than plain overloaded functions.
A library of polymorphic instances is a set of building blocks to construct code that the compiler will assemble on its own, given nothing but the desired type.
Polymorphic functions that take instance arguments are latent requests to the type class mechanism to assemble helper functions behind the scenes.
The API's clients are freed from the burden of plumbing together all of the necessary building blocks by hand.


## Exercises

### Even Number Literals

Write an instance of `OfNat` for the even number datatype from the [previous section's exercises](pos.md#even-numbers) that uses recursive instance search.
