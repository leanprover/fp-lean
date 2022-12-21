# Alternatives


## Recovery from Failure

`Validate` can also be used in situations where there is more than one way for input to be acceptable.
For the input form `RawInput`, an alternative set of business rules that implement conventions from a legacy system might be the following:

 0. All human users must provide a birth year that is four digits.
 1. Users born prior to 1970 do not need to provide names, due to incomplete older records.
 2. Users born after 1970 must provide names.
 3. Companies should enter `"FIRM"` as their year of birth instead and provide a company name.
 
No particular provision is made for users born in 1970.
It is expected that they will either give up, lie about their year of birth, or call.
The company considers this an acceptable cost of doing business.
 
The following inductive type captures the values that can be produced from these stated rules:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean LegacyCheckedInput}}
```

A validator for these rules is more complicated, however, as it must address all three cases.
While it can be written as a series of nested `if` expressions, it's easier to design the three cases independently and then combine them.
This requires a means of recovering from failure while preserving error messages:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ValidateorElse}}
```

This pattern of recovery from failures is common enough that Lean has built-in syntax for it, attached to a type class named `OrElse`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean OrElse}}
```
The expression `{{#example_in Examples/FunctorApplicativeMonad.lean OrElseSugar}}` is short for `{{#example_out Examples/FunctorApplicativeMonad.lean OrElseSugar}}`.
An instance of `OrElse` for `Validate` allows this syntax to be used for error recovery:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean OrElseValidate}}
```

The validator for `LegacyCheckedInput` can be built from a validator for each constructor.
The rules for a company state that the birth year should be the string `"FIRM"` and that the name should be non-empty.
The constructor `LegacyCheckedInput.company`, however, has no representation of the birth year at all, so there's no easy way to carry it out using `<*>`.
The key is to use a function with `<*>` that ignores its argument.

Checking that a Boolean condition holds without recording any evidence of this fact in a type can be accomplished with `checkThat`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkThat}}
```
This definition of `checkCompany` uses `checkThat`, and then throws away the resulting `Unit` value:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkCompanyProv}}
```
However, this definition is quite noisy.

It can be simplified using two improvements.
The first is to replace the first use of `<*>` with a specialized version that automatically ignores the value returned by the first argument, called `*>`.
This operator is also controlled by a type class, called `SeqRight`, and `{{#example_in Examples/FunctorApplicativeMonad.lean seqRightSugar}}` is syntactic sugar for `{{#example_out Examples/FunctorApplicativeMonad.lean seqRightSugar}}`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ClassSeqRight}}
```
There is a default implementation of `seqRight` in terms of `seq`: `seqRight (a : f α) (b : Unit → f β) : f β := pure (fun _ x => x) <*> a <*> b ⟨⟩`.

Using `seqRight`, `checkCompany` becomes simpler:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkCompanyProv2}}
```
One more simplification is possible.
For every `Applicative`, `pure F <*> E` is equivalent to `f <$> E`.
In other words, using `seq` to apply a function that was placed into the `Applicative` type using `pure` is overkill, and the function could have just been applied using `Functor.map`.
This simplification yields:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkCompany}}
```

The remaining two constructors of `LegacyCheckedInput` use subtypes for their fields.
A general-purpose tool for checking subtypes will make these easier to read:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkSubtype}}
```
In the function's argument list, it's important that the type class `[Decidable (p v)]` occur after the specification of the arguments `v` and `p`.
Otherwise, it would refer to an additional set of automatic implicit arguments, rather than to the manually-provided values.
The `Decidable` instance is what allows the proposition `p v` to be checked using `if`.

Checking both human cases is a combination of the tool discovered so far:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkHumanBefore1970}}

{{#example_decl Examples/FunctorApplicativeMonad.lean checkHumanAfter1970}}
```

The validators for the three cases can be combined using `<|>`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkLegacyInput}}
```

The successful cases return constructors of `LegacyCheckedInput`, as expected:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean trollGroomers}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean trollGroomers}}
```
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean johnny}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean johnny}}
```

The worst possible input returns all the possible failures:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean allFailures}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean allFailures}}
```


## The `Alternative` Class

Many types support a notion of failure and recovery.
The `Many` monad from the section on [evaluating arithmetic expressions in a variety of monads#nondeterministic-search](../monads/arithmetic.md) is one such type, as is `Option`.
Both support failure without providing a reason (unlike, say, `Except` and `Validate`, which require some indication of what went wrong).

The `Alternative` class describes applicative functors that have additional operators for failure and recovery:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean FakeAlternative}}
```
Just as implementors of `Add α` get `HAdd α α α` instances for free, implementors of `Alternative` get `OrElse` instances for free:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean AltOrElse}}
```

The implementation of `Alternative` for `Option` keeps the first none-`none` argument:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean AlternativeOption}}
```
Similarly, the implementation for `Many` follows the general structure of `Many.union`, with minor differences due to the laziness-inducing `Unit` parameters being placed differently:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean AlternativeMany}}
```

Like other type classes, `Alternative` enables the definition of a variety of operations that work for _any_ applicative functor that implements `Alternative`.
One of the most important is `guard`, which causes `failure` when a decidable proposition is false:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean guard}}
```
It is very useful in monadic programs to terminate execution early.
In `Many`, it can be used to filter out a whole branch of a search, as in the following program that computes all even divisors of a natural number:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean evenDivisors}}
```
Running it on `20` yields the expected results:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean evenDivisors20}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean evenDivisors20}}
```


## Exercises

### Improve Validation Friendliness

The errors returned from `Validate` programs that use `<|>` can be difficult to read, because inclusion in the list of errors simply means that the error can be reached through _some_ code path.
A more structured error report can be used to guide the user through the process more accurately:

 * Replace the `NonEmptyList` in `Validate.error` with a bare type variable, and then update the definitions of the `Applicative (Validate ε)` and `OrElse (Validate ε α)` instances to require only that there be an `Append ε` instance available.
 * Define a function `Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α` that transforms all the errors in a validation run.
 * Using the datatype `TreeError` to represent errors, rewrite the legacy validation system to track its path through the three alternatives.
 * Write a function `report : TreeError → String` that outputs a user-friendly view of the `TreeError`'s accumulated warnings and errors.
 
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean TreeError}}
```


