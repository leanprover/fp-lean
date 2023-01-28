# Applicative Functors

An _applicative functor_ is a functor that has two additional operations available: `pure` and `seq`.
`pure` is the same operator used in `Monad`, because `Monad` in fact inherits from `Applicative`.
`seq` is much like `map`: it allows a function to be used in order to transform the contents of a datatype.
However, with `seq`, the function is itself contained in the datatype: `{{#example_out Examples/FunctorApplicativeMonad.lean seqType}}`.
Having the function under the type `f` allows the `Applicative` instance to control how the function is applied, while `Functor.map` unconditionally applies a function.
The second argument has a type that begins with `Unit →` to allow the definition of `seq` to short-circuit in cases where the function will never be applied.

The value of this short-circuiting behavior can be seen in the instance of `Applicative Option`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ApplicativeOption}}
```
In this case, if there is no function for `seq` to apply, then there is no need to compute its argument, so `x` is never called.
The same consideration informs the instance of `Applicative` for `Except`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ApplicativeExcept}}
```
This short-circuiting behavior depends only on the `Option` or `Except` structures that _surround_ the function, rather than on the function itself.

Monads can be seen as a way of capturing the notion of sequentially executing statements into a pure functional language.
The result of one statement can affect which further statements run.
This can be seen in the type of `bind`: `{{#example_out Examples/FunctorApplicativeMonad.lean bindType}}`.
The first statement's resulting value is an input into a function that computes the next statement to execute.
Successive uses of `bind` are like a sequence of statements in an imperative programming language, and `bind` is powerful enough to implement control structures like conditionals and loops.

Following this analogy, `Applicative` captures function application in a language that has side effects.
The arguments to a function in languages like Kotlin or C# are evaluated from left to right.
Side effects performed by earlier arguments occur before those performed by later arguments.
A function is not powerful enough to implement custom short-circuiting operators that depend on the specific _value_ of an argument, however.

Typically, `seq` is not invoked directly.
Instead, the operator `<*>` is used.
This operator wraps its second argument in `fun () => ...`, simplifying the call site.
In other words, `{{#example_in Examples/FunctorApplicativeMonad.lean seqSugar}}` is syntactic sugar for `{{#example_out Examples/FunctorApplicativeMonad.lean seqSugar}}`.


The key feature that allows `seq` to be used with multiple arguments is that a multiple-argument Lean function is really a single-argument function that returns another function that's waiting for the rest of the arguments.
In other words, if the first argument to `seq` is awaiting multiple arguments, then the result of the `seq` will be awaiting the rest.
For example, `{{#example_in Examples/FunctorApplicativeMonad.lean somePlus}}` can have the type `{{#example_out Examples/FunctorApplicativeMonad.lean somePlus}}`.
Providing one argument, `{{#example_in Examples/FunctorApplicativeMonad.lean somePlusFour}}`, results in the type `{{#example_out Examples/FunctorApplicativeMonad.lean somePlusFour}}`.
This can itself be used with `seq`, so `{{#example_in Examples/FunctorApplicativeMonad.lean somePlusFourSeven}}` has the type `{{#example_out Examples/FunctorApplicativeMonad.lean somePlusFourSeven}}`.

Not every functor is applicative.
`Pair` is like the built-in product type `Prod`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean Pair}}
```
Like `Except`, `{{#example_in Examples/FunctorApplicativeMonad.lean PairType}}` has type `{{#example_out Examples/FunctorApplicativeMonad.lean PairType}}`.
This means that `Pair α` has type `Type → Type`, and a `Functor` instance is possible:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean FunctorPair}}
```
This instance obeys the `Functor` contract.

The two properties to check are that `{{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapId 0}} = {{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapId 2}}` and that `{{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapComp1 0}} = {{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapComp2 0}}`.
The first property can be checked by just stepping through the evaluation of the left side, and noticing that it evaluates to the right side:
```lean
{{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapId}}
```
The second can be checked by stepping through both sides, and noting that they yield the same result:
```lean
{{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapComp1}}

{{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapComp2}}
```

Attempting to define an `Applicative` instance, however, does not work so well.
It will require a definition of `pure`:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean Pairpure}}
```
```output error
{{#example_out Examples/FunctorApplicativeMonad.lean Pairpure}}
```
There is a value with type `β` in scope (namely `x`), and the error message from the underscore suggests that the next step is to use the constructor `Pair.mk`:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean Pairpure2}}
```
```output error
{{#example_out Examples/FunctorApplicativeMonad.lean Pairpure2}}
```
Unfortunately, there is no `α` available.
Because `pure` would need to work for _all possible types_ α to define an instance of `Applicative (Pair α)`, this is impossible.
After all, a caller could choose `α` to be `Empty`, which has no values at all.

## A Non-Monadic Applicative

When validating user input to a form, it's generally considered to be best to provide many errors at once, rather than one error at a time.
This allows the user to have an overview of what is needed to please the computer, rather than feeling badgered as they correct the errors field by field.

Ideally, validating user input will be visible in the type of the function that's doing the validating.
It should return a datatype that is specific—checking that a text box contains a number should return an actual numeric type, for instance.
A validation routine could throw an exception when the input does not pass validation.
Exceptions have a major drawback, however: they terminate the program at the first error, making it impossible to accumulate a list of errors.

On the other hand, the common design pattern of accumulating a list of errors and then failing when it is non-empty is also problematic.
A long nested sequences of `if` statements that validate each sub-section of the input data is hard to maintain, and it's easy to lose track of an error message or two.
Ideally, validation can be performed using an API that enables a new value to be returned yet automatically tracks and accumulates error messages.

An applicative functor called `Validate` provides one way to implement this style of API.
Like the `Except` monad, `Validate` allows a new value to be constructed that characterizes the validated data accurately.
Unlike `Except`, it allows multiple errors to be accumulated, without a risk of forgetting to check whether the list is empty.

### User Input
As an example of user input, take the following structure:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean RawInput}}
```
The business logic to be implemented is the following:
 1. The name may not be empty
 2. The birth year must be numeric and non-negative
 3. The birth year must be greater than 1900, and less than or equal to the year in which the form is validated
 
Representing these as a datatype will require a new feature, called _subtypes_.
With this tool in hand, a validation framework can be written that uses an applicative functor to track errors, and these rules can be implemented in the framework.
 
### Subtypes
Representing these conditions is easiest with one additional Lean type, called `Subtype`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean Subtype}}
```
This structure has two type parameters: an implicit parameter that is the type of data `α`, and an explicit parameter `p` that is a predicate over `α`.
A _predicate_ is a logical statement with a variable in it that can be replaced with a value to yield an actual statement, like the [parameter to `GetElem`](../type-classes/indexing.md#overloading-indexing) that describes what it means for an index to be in bounds for a lookup.
In the case of `Subtype`, the predicate slices out some subset of the values of `α` for which the predicate holds.
The structure's two fields are, respectively, a value from `α` and evidence that the value satisfies the predicate `p`.
Lean has special syntax for `Subtype`.
If `p` has type `α → Prop`, then the type `Subtype p` can also be written `{{#example_out Examples/FunctorApplicativeMonad.lean subtypeSugar}}`, or even `{{#example_out Examples/FunctorApplicativeMonad.lean subtypeSugar2}}` when the type can be inferred automatically.

[Representing positive numbers as inductive types](../type-classes/pos.md) is clear and easy to program with.
However, it has a key disadvantage.
While `Nat` and `Int` have the structure of ordinary inductive types from the perspective of Lean programs, the compiler treats them specially and uses fast arbitrary-precision number libraries to implement them.
This is not the case for additional user-defined types.
However, a subtype of `Nat` that restricts it to non-zero numbers allows the new type to use the efficient representation while still ruling out zero at compile time:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean FastPos}}
```

The smallest fast positive number is still one.
Now, instead of being a constructor of an inductive type, it's an instance of a structure that's constructed with angle brackets.
The first argument is the underlying `Nat`, and the second argument is the evidence that said `Nat` is greater than zero:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean one}}
```
The `OfNat` instance is very much like that for `Pos`, except it uses a short tactic proof to provide evidence that `n + 1 > 0`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean OfNatFastPos}}
```
The `simp_arith` tactic is a version of `simp` that takes additional arithmetic identities into account.

Subtypes are a two-edged sword.
They allow efficient representation of validation rules, but they transfer the burden of maintaining these rules to the users of the library, who have to _prove_ that they are not violating important invariants.
Generally, it's a good idea to use them internally to a library, providing an API to users that automatically ensures that all invariants are satisfied, with any necessary proofs being internal to the library.

Checking whether a value of type `α` is in the subtype `{x : α // p x}` usually requires that the proposition `p x` be decidable.
The [section on equality and ordering classes](../type-classes/standard-classes.md#equality-and-ordering) describes how decidable propositions can be used with `if`.
When `if` is used with a decidable proposition, a name can be provided.
In the `then` branch, the name is bound to evidence that the proposition is true, and in the `else` branch, it is bound to evidence that the proposition is false.
This comes in handy when checking whether a given `Nat` is positive:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean NatFastPos}}
```
In the `then` branch, `h` is bound to evidence that `n > 0`, and this evidence can be used as the second argument to `Subtype`'s constructor.


### Validated Input

The validated user input is a structure that expresses the business logic using multiple techniques:
 * The structure type itself encodes the year in which it was checked for validity, so that `CheckedInput 2019` is not the same type as `CheckedInput 2020`
 * The birth year is represented as a `Nat` rather than a `String`
 * Subtypes are used to constrain the allowed values in the name and birth year fields
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean CheckedInput}}
```

An input validator should take the current year and a `RawInput` as arguments, returning either a checked input or at least one validation failure.
This is represented by the `Validate` type:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean Validate}}
```
It looks very much like `Except`.
The only difference is that the `error` constructor may contain more than one failure.

Validate is a functor.
Mapping a function over it transforms any successful value that might be present, just as in the `Functor` instance for `Except`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean FunctorValidate}}
```

The `Applicative` instance for `Validate` has an important difference from the instance for `Except`: while the instance for `Except` terminates at the first error encountered, the instance for `Validate` is careful to accumulate all errors from _both_ the function and the argument branches:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ApplicativeValidate}}
```

Using `.errors` together with the constructor for `NonEmptyList` is a bit verbose.
Helpers like `reportError` make code more readable.
In this application, error reports will consist of field names paired with messages:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean Field}}

{{#example_decl Examples/FunctorApplicativeMonad.lean reportError}}
```

The `Applicative` instance for `Validate` allows the checking procedures for each field to be written independently and then composed.
Checking a name consists of ensuring that a string is non-empty, then returning evidence of this fact in the form of a `Subtype`.
This uses the evidence-binding version of `if`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkName}}
```
In the `then` branch, `h` is bound to evidence that `name = ""`, while it is bound to evidence that `¬name = ""` in the `else` branch.

It's certainly the case that some validation errors make other checks impossible.
For example, it makes no sense to check whether the birth year field is greater than 1900 if a confused user wrote the word `"syzygy"` instead of a number.
Checking the allowed range of the number is only meaningful after ensuring that the field in fact contains a number.
This can be expressed using the function `andThen`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ValidateAndThen}}
```
While this function's type signature makes it suitable to be used as `bind` in a `Monad` instance, there are good reasons not to do so.
They are described [in the section that describes the `Applicative` contract](applicative-contract.md#additional-stipulations).

To check that the birth year is a number, a built-in function called `String.toNat? : String → Option Nat` is useful.
It's most user-friendly to eliminate leading and trailing whitespace first:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkYearIsNat}}
```
To check that the provided year is in the expected range, nested uses of the evidence-providing form of `if` are in order:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkBirthYear}}
```

Finally, these three components can be combined using `seq`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean checkInput}}
```

Testing `checkInput` shows that it can indeed return multiple pieces of feedback:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean checkDavid1984}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean checkDavid1984}}
```
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean checkBlank2045}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean checkBlank2045}}
```
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean checkDavidSyzygy}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean checkDavidSyzygy}}
```


Form validation with `checkInput` illustrates a key advantage of `Applicative` over `Monad`.
Because `>>=` provides enough power to modify the rest of the program's execution based on the value from the first step, it _must_ receive a value from the first step to pass on.
If no value is received (e.g. because an error has occurred), then `>>=` cannot execute the rest of the program.
`Validate` demonstrates why it can be useful to run the rest of the program anyway: in cases where the earlier data isn't needed, running the rest of the program can yield useful information (in this case, more validation errors).
`Applicative`'s `<*>` may run both of its arguments before recombining the results.
Similarly, `>>=` forces sequential execution.
Each step must complete before the next may run.
This is generally useful, but it makes it impossible to have parallel execution of different threads that naturally emerges from the program's actual data dependencies.
A more powerful abstraction like `Monad` increases the flexibility that's available to the API consumer, but it decreases the flexibility that is available to the API implementor.

