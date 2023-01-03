# The Complete Definitions

Now that all the relevant language features have been presented, this section describes the complete, honest definitions of `Functor`, `Applicative`, and `Monad` as they occur in the Lean standard library.
For the sake of understanding, no details are omitted.

## Functor

The complete definition of the `Functor` class makes use of universe polymorphism and a default method implementation:
```lean
{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean HonestFunctor}}
```
In this definition, `Function.comp` is function composition, which is typically written with the `∘` operator.
`Function.const` is the _constant function_, which is a two-argument function that ignores its second argument.
Applying this function to only one argument produces a function that always returns the same value, which is useful when an API demands a function but a program doesn't need to compute different results for different arguments.
A simple version of `Function.const` can be written as follows:
```lean
{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean simpleConst}}
```
Using it with one argument as the function argument to `List.map` demonstrates its utility:
```lean
{{#example_in Examples/FunctorApplicativeMonad/ActualDefs.lean mapConst}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad/ActualDefs.lean mapConst}}
```
The actual function has the following signature:
```output info
{{#example_out Examples/FunctorApplicativeMonad/ActualDefs.lean FunctionConstType}}
```
Here, the type argument `β` is an explicit argument, so the default definition of `Functor.mapConst` provides an `_` argument that instructs Lean to find a unique type to pass to `Function.const` that would cause the program to type check.
`{{#example_in Examples/FunctorApplicativeMonad/ActualDefs.lean unfoldCompConst}}` is equivalent to `{{#example_out Examples/FunctorApplicativeMonad/ActualDefs.lean unfoldCompConst}}`.

The `Functor` type class inhabits a universe that is the greater of `u+1` and `v`.
Here, `u` is the level of universes accepted as arguments to `f`, while `v` is the universe returned by `f`.
To see why the structure that implements the `Functor` type class must be in a universe that's larger than `u`, begin with a simplified definition of the class:
```lean
{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean FunctorSimplified}}
```
This type class's structure type is equivalent to the following inductive type:
```lean
{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean FunctorDatatype}}
```
The implementation of the `map` method that is passed as an argument to `Functor.mk` contains a function that takes two types in `Type u` as arguments.
This means that the function itself is a `Type (u+1)`, so `Functor` must also be at a level that is at least `u+1`.
All the type classes in this section share this property.

## Applicative

The `Applicative` type class is actually built from a number of smaller classes that each implement some of the relevant methods.

