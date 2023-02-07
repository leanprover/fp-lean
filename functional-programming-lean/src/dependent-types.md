# Programming with Dependent Types

In most statically-typed programming languages, the world of types and the world of programs are separated.
Types and programs have different grammars and they are used at different times.
Types are typically used at compile time, to check that a program obeys certain invariants.
Programs are used at run time, to actually perform computations.
When the two interact, it is usually in the form of a type-case operator like an "instance-of" check or a casting operator that provides the type checker with information that was otherwise unavailable, to be verified at run time.
In other words, the interaction consists of types being inserted into the world of programs, gaining some limited run-time meaning.

Lean does not impose this strict separation.
In Lean, programs may compute types and types may contain programs.
Types are first-class participants in the programming process.

_Dependent types_ are types that contain non-type expressions.
A common source of dependent types is a named argument to a function.
For example, the function `natOrStringThree` returns either a natural number or a string, depending on which `Bool` it is passed:
```lean
{{#example_decl Examples/DependentTypes.lean natOrStringThree}}
```

Further examples of dependent types include:
 * [The introductory section on polymorphism](getting-to-know/polymorphism.md) contains `posOrNegThree`, in which the function's return type depends on the value of the argument;
 * [The `OfNat` type class](type-classes/pos.md#literal-numbers) depends on the specific natural number literal being used;
 * [The `CheckedInput` structure](functor-applicative-monad/applicative.md#validated-input) used in the example of validators depends on the year in which validation occurred; and
 * [Subtypes](functor-applicative-monad/applicative.md#subtypes) contain propositions that refer to particular values,
 * Essentially all interesting propositions, including those that determine the validity of [array indexing notation](props-proofs-indexing.md), are types that contain values and are thus dependent types.

Dependent types vastly increase the power of a type system.
The flexibility of return types that branch on argument values enables programs to be written that cannot easily be given types in other type systems.
The power of d

TODO write a couple sentences about why DT both allows more programs and stronger invariants, give warning about tying in knots

