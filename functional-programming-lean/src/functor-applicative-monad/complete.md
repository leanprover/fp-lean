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
This means that the type of the function itself is in `Type (u+1)`, so `Functor` must also be at a level that is at least `u+1`.
Similarly, other arguments to the function have a type built by applying `f`, so it must also have a level that is at least `v`.
All the type classes in this section share this property.

## Applicative

The `Applicative` type class is actually built from a number of smaller classes that each contain some of the relevant methods.
The first are `Pure` and `Seq`, which contain `pure` and `seq` respectively:
```lean
{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean Pure}}

{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean Seq}}
```

In addition to these, `Applicative` also depends on `SeqRight` and an analogous `SeqLeft` class:
```lean
{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean SeqRight}}

{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean SeqLeft}}
```

The `seqRight` function, which was introduced in the [section about alternatives and validation](alternative.md), is easiest to understand from the perspective of effects.
`{{#example_in Examples/FunctorApplicativeMonad.lean seqRightSugar}}`, which desugars to `{{#example_out Examples/FunctorApplicativeMonad.lean seqRightSugar}}`, can be understood as first executing `E1`, and then `E2`, resulting only in `E2`'s result.
Effects from `E1` may result in `E2` not being run, or being run multiple times.
Indeed, if `f` has a `Monad` instance, then `E1 *> E2` is equivalent to `do let _ ← E1; E2`, but `seqRight` can be used with types like `Validate` that are not monads.

Its cousin `seqLeft` is very similar, except the leftmost expression's value is returned.
`{{#example_in Examples/FunctorApplicativeMonad/ActualDefs.lean seqLeftSugar}}` desugars to `{{#example_out Examples/FunctorApplicativeMonad/ActualDefs.lean seqLeftSugar}}`.
`{{#example_in Examples/FunctorApplicativeMonad/ActualDefs.lean seqLeftType}}` has type `{{#example_out Examples/FunctorApplicativeMonad/ActualDefs.lean seqLeftType}}`, which is identical to that of `seqRight` except for the fact that it returns `f α`.
`{{#example_in Examples/FunctorApplicativeMonad/ActualDefs.lean seqLeftSugar}}` can be understood as a program that first executes `E1`, and then `E2`, returning the original result for `E1`.
If `f` has a `Monad` instance, then `E1 <* E2` is equivalent to `do let x ← E1; _ ← E2; pure x`.
Generally speaking, `seqLeft` is useful for specifying extra conditions on a value in a validation or parser-like workflow without changing the value itself.

The definition of `Applicative` extends all these classes, along with `Functor`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean Applicative}}
```
A complete definition of `Applicative` requires only definitions for `pure` and `seq`.
This is because there are default definitions for all of the methods from `Functor`, `SeqLeft`, and `SeqRight`.
The `mapConst` method of `Functor` has its own default implementation in terms of `Functor.map`.
These default implementations should only be overridden with new functions that are behaviorally equivalent, but more efficient.
The default implementations should be seen as specifications for correctness as well as automatically-created code.

The default implementation for `seqLeft` is very compact.
Replacing some of the names with their syntactic sugar or their definitions can provide another view on it, so:
```lean
{{#example_in Examples/FunctorApplicativeMonad/ActualDefs.lean unfoldMapConstSeqLeft}}
```
becomes
```lean
{{#example_out Examples/FunctorApplicativeMonad/ActualDefs.lean unfoldMapConstSeqLeft}}
```
How should `(fun x _ => x) <$> a` be understood?
Here, `a` has type `f α`, and `f` is a functor.
If `f` is `List`, then `{{#example_in Examples/FunctorApplicativeMonad/ActualDefs.lean mapConstList}}` evaluates to `{{#example_out Examples/FunctorApplicativeMonad/ActualDefs.lean mapConstList}}`.
If `f` is `Option`, then `{{#example_in Examples/FunctorApplicativeMonad/ActualDefs.lean mapConstOption}}` evaluates to `{{#example_out Examples/FunctorApplicativeMonad/ActualDefs.lean mapConstOption}}`.
In each case, the values in the functor are replaced by functions that return the original value, ignoring their argument.
When combined with `seq`, this function discards the values from `seq`'s second argument.

The default implementation for `seqRight` is very similar, except `const` has an additional argument `id`.
This definition can be understood similarly, by first introducing some standard syntactic sugar and then replacing some names with their definitions:
```lean
{{#example_eval Examples/FunctorApplicativeMonad/ActualDefs.lean unfoldMapConstSeqRight}}
```
How should `(fun _ x => x) <$> a` be understood?
Once again, examples are useful.
`{{#example_in Examples/FunctorApplicativeMonad/ActualDefs.lean mapConstIdList}}` is equivalent to `{{#example_out Examples/FunctorApplicativeMonad/ActualDefs.lean mapConstIdList}}`, and `{{#example_in Examples/FunctorApplicativeMonad/ActualDefs.lean mapConstIdOption}}` is equivalent to `{{#example_out Examples/FunctorApplicativeMonad/ActualDefs.lean mapConstIdOption}}`.
In other words, `(fun _ x => x) <$> a` preserves the overall shape of `a`, but each value is replaced by the identity function.
From the perspective of effects, the side effects of `a` occur, but the values are thrown out when it is used with `seq`.

## Monad

Just as the constituent operations of `Applicative` are split into their own type classes, `Bind` has its own class as well:
```lean
{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean Bind}}
```
`Monad` extends `Applicative` with `Bind`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean Monad}}
```
Tracing the collection of inherited methods and default methods from the entire hierarchy shows that a `Monad` instance requires only implementations of `bind` and `pure`.
In other words, `Monad` instances automatically yield implementations of `seq`, `seqLeft`, `seqRight`, `map`, and `mapConst`.
From the perspective of API boundaries, any type with a `Monad` instance gets instances for `Bind`, `Pure`, `Seq`, `Functor`, `SeqLeft`, and `SeqRight`.


## Exercises

 1. Understand the default implementations of `map`, `seq`, `seqLeft`, and `seqRight` in `Monad` by working through examples such as `Option` and `Except`. In other words, substitute their definitions for `bind` and `pure` into the default definitions, and simplify them to recover the versions `map`, `seq`, `seqLeft`, and `seqRight` that would be written by hand.
 2. On paper or in a text file, prove to yourself that the default implementations of `map` and `seq` satisfy the contracts for `Functor` and `Applicative`. In this argument, you're allowed to use the rules from the `Monad` contract as well as ordinary expression evaluation.
