# Ordering Monad Transformers

When composing a monad from a stack of monad transformers, it's important to be aware that the order in which the monad transformers are layered matters.
Different orderings of the same set of transformers result in different monads.

This version of `countLetters` is just like the previous version, except it uses type classes to describe the set of available effects instead of providing a concrete monad:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean countLettersClassy}}
```
The state and exception monad transformers can be combined in two different orders, each resulting in a monad that has instances of both type classes:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean SomeMonads}}
```

When run on input for which the program does not throw an exception, both monads yield similar results:
```lean
{{#example_in Examples/MonadTransformers/Defs.lean countLettersM1Ok}}
```
```output info
{{#example_out Examples/MonadTransformers/Defs.lean countLettersM1Ok}}
```
```lean
{{#example_in Examples/MonadTransformers/Defs.lean countLettersM2Ok}}
```
```output info
{{#example_out Examples/MonadTransformers/Defs.lean countLettersM2Ok}}
```
However, there is a subtle difference between these return values.
In the case of `M1`, the outermost constructor is `Except.ok`, and it contains a pair of the unit constructor with the final state.
In the case of `M2`, the outermost constructor is the pair, which contains `Except.ok` applied only to the unit constructor.
The final state is outside of `Except.ok`.
In both cases, the program returns the counts of vowels and consonants.

On the other hand, only one monad yields a count of vowels and consonants when the string causes an exception to be thrown.
Using `M1`, only an exception value is returned:
```lean
{{#example_in Examples/MonadTransformers/Defs.lean countLettersM1Error}}
```
```output info
{{#example_out Examples/MonadTransformers/Defs.lean countLettersM1Error}}
```
Using `M2`, the exception value is paired with the state as it was at the time that the exception was thrown:
```lean
{{#example_in Examples/MonadTransformers/Defs.lean countLettersM2Error}}
```
```output info
{{#example_out Examples/MonadTransformers/Defs.lean countLettersM2Error}}
```

It might be tempting to think that `M2` is superior to `M1` because it provides more information that might be useful when debugging.
The same program might compute _different_ answers in `M1` than it does in `M2`, and there's no principled reason to say that one of these answers is necessarily better than the other.
This can be seen by adding a step to the program that handles exceptions:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean countWithFallback}}
```
This program always succeeds, but it might succeed with different results.
If no exception is thrown, then the results are the same as `countLetters`:
```lean
{{#example_in Examples/MonadTransformers/Defs.lean countWithFallbackM1Ok}}
```
```output info
{{#example_out Examples/MonadTransformers/Defs.lean countWithFallbackM1Ok}}
```
```lean
{{#example_in Examples/MonadTransformers/Defs.lean countWithFallbackM2Ok}}
```
```output info
{{#example_out Examples/MonadTransformers/Defs.lean countWithFallbackM2Ok}}
```
However, if the exception is thrown and caught, then the final states are very different.
With `M1`, the final state contains only the letter counts from `"Fallback"`:
```lean
{{#example_in Examples/MonadTransformers/Defs.lean countWithFallbackM1Error}}
```
```output info
{{#example_out Examples/MonadTransformers/Defs.lean countWithFallbackM1Error}}
```
With `M2`, the final state contains letter counts from both `"hello"` and from `"Fallback"`, as one would expect in an imperative language:
```lean
{{#example_in Examples/MonadTransformers/Defs.lean countWithFallbackM2Error}}
```
```output info
{{#example_out Examples/MonadTransformers/Defs.lean countWithFallbackM2Error}}
```

In `M1`, throwing an exception "rolls back" the state to where the exception was caught.
In `M2`, modifications to the state persist across the throwing and catching of exceptions.
This difference can be seen by unfolding the definitions of `M1` and `M2`.
`{{#example_in Examples/MonadTransformers/Defs.lean M1eval}}` unfolds to `{{#example_out Examples/MonadTransformers/Defs.lean M1eval}}`, and `{{#example_in Examples/MonadTransformers/Defs.lean M2eval}}` unfolds to `{{#example_out Examples/MonadTransformers/Defs.lean M2eval}}`.
That is to say, `M1 α` describes functions that take an initial letter count, returning either an error or an `α` paired with updated counts.
When an exception is thrown in `M1`, there is no final state.
`M2 α` describes functions that take an initial letter count and return a new letter count paired with either an error or an `α`.
When an exception is thrown in `M2`, it is accompanied by a state.

## Commuting Monads

In the jargon of functional programming, two monad transformers are said to _commute_ if they can be re-ordered without the meaning of the program changing.
The fact that the result of the program can differ when `StateT` and `ExceptT` are reordered means that state and exceptions do not commute.
In general, monad transformers should not be expected to commute.

Even though not all monad transformers commute, some do.
For example, two uses of `StateT` can be re-ordered.
Expanding the definitions in `{{#example_in Examples/MonadTransformers/Defs.lean StateTDoubleA}}` yields the type `{{#example_out Examples/MonadTransformers/Defs.lean StateTDoubleA}}`, and `{{#example_in Examples/MonadTransformers/Defs.lean StateTDoubleB}}` yields `{{#example_out Examples/MonadTransformers/Defs.lean StateTDoubleB}}`.
In other words, the differences between them are that they nest the `σ` and `σ'` types in different places in the return type, and they accept their arguments in a different order.
Any client code will still need to provide the same inputs, and it will still receive the same outputs.

Most programming languages that have both mutable state and exceptions work like `M2`.
In those languages, state that _should_ be rolled back when an exception is thrown is difficult to express, and it usually needs to be simulated in a manner that looks much like the passing of explicit state values in `M1`.
Monad transformers grant the freedom to choose an interpretation of effect ordering that works for the problem at hand, with both choices being equally easy to program with.
However, they also require care to be taken in the choice of ordering of transformers.
With great expressive power comes the responsibility to check that what's being expressed is what is intended, and the type signature of `countWithFallback` is probably more polymorphic than it should be.


## Exercises

 * Check that `ReaderT` and `StateT` commute by expanding their definitions and reasoning about the resulting types.
 * Do `ReaderT` and `ExceptT` commute? Check your answer by expanding their definitions and reasoning about the resulting types.
 * Construct a monad transformer `ManyT` based on the definition of `Many`, with a suitable `Alternative` instance. Check that it satisfies the `Monad` contract.
 * Does `ManyT` commute with `StateT`? If so, check your answer by expanding definitions and reasoning about the resulting types. If not, write a program in `ManyT (StateT σ Id)` and a program in `StateT σ (ManyT Id)`. Each program should be one that makes more sense for the given ordering of monad transformers.
