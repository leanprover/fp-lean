# Coercions

In mathematics, it is common to use the same symbol to stand for different aspects of some object in different contexts.
For example, if a ring is referred to in a context where a set is expected, then it is understood that the ring's underlying set is what's intended.
In programming languages, it is common to have rules to automatically translate values of one type into values of another type.
For instance, Java allows a `byte` to be automatically promoted to an `int`, and Kotlin allows a non-nullable type to be used in a context that expects a nullable version of the type.

In Lean, both purposes are served by a mechanism called _coercions_.
When Lean encounters an expression of one type in a context that expects a different type, it will attempt to coerce the expression before reporting a type error.
Unlike Java, C, and Kotlin, the coercions are extensible by defining instances of type classes.

## Positive Numbers

For example, every positive number corresponds to a natural number.
The function `Pos.toNat` converts a `Pos` to the corresponding `Nat`:
```lean
{{#example_decl Examples/Classes.lean posToNat}}
```
The function `List.drop`, with type `{{#example_out Examples/Classes.lean drop}}`, removes a prefix of a list.
Applying `List.drop` to a `Pos`, however, leads to a type error:
```lean
{{#example_in Examples/Classes.lean dropPos}}
```
```output error
{{#example_out Examples/Classes.lean dropPos}}
```

The type class `Coe` describes overloaded ways of coercing from one type to another:
```lean
{{#example_decl Examples/Classes.lean Coe}}
```
An instance of `Coe Pos Nat` is enough to allow the prior code to work:
```lean
{{#example_decl Examples/Classes.lean CoePosNat}}

{{#example_in Examples/Classes.lean dropPosCoe}}
```
```output info
{{#example_out Examples/Classes.lean dropPosCoe}}
```
Using `#check` shows the result of the instance search that was used behind the scenes:
```lean
{{#example_in Examples/Classes.lean checkDropPosCoe}}
```
```output info
{{#example_out Examples/Classes.lean checkDropPosCoe}}
```

## Options and Chaining Coercions

The `Option` type can be used similarly to nullable types in C# and Kotlin: the `none` constructor represents the absence of a value.
The Lean standard library defines an instance of `Coe α (Option α)` that wraps the argument to `coe` in `some`:
```lean
{{#example_decl Examples/Classes.lean CoeOption}}
```
This allows option types to be used in manner even more similar to nullable types, because `some` can be omitted.
For instance, the function `List.getLast?` that finds the last entry in a list can be written without a `some` around the return value `x`:
```lean
{{#example_decl Examples/Classes.lean lastHuh}}
```
Instance search finds the `Coe` instance, and inserts a call to `coe`, which wraps the argument in `some`.

Coercions may also be chained.
For instance, a `String` may be used in a context that expects an `Option (Option (Option String))`:
```lean
{{#example_decl Examples/Classes.lean perhapsPerhapsPerhaps}}
```
The result of `{{#example_in Examples/Classes.lean evalPerhaps}}` is `{{#example_out Examples/Classes.lean evalPerhaps}}`, demonstrating that `Coe.coe` was used three times.

## Non-Empty Lists and Dependent Coercions

An instance of `Coe α β` makes sense when the type `β` has a value that can represent each value from the type `α`.
Coercing from `Nat` to `Int` makes sense, because the type `Int` contains all the natural numbers.
Similarly, a coercion from non-empty lists to ordinary lists makes sense because the `List` type can represent every non-empty list:
```lean
{{#example_decl Examples/Classes.lean CoeNEList}}
```
This allows non-empty lists to be used with the entire `List` API.

On the other hand, it is impossible to write an instance of `Coe (List α) (NonEmptyList α)`, because there's no non-empty list that can represent the empty list.
This limitation can be worked around by using another version of coercions, which are called _dependent coercions_.
Dependent coercions can be used when the ability to coerce from one type to another depends on which particular value is being coerced.
Just as the `OfNat` type class takes the particular `Nat` being overloaded as a parameter, dependent coercion takes the value being coerced as a parameter:
```lean
{{#example_decl Examples/Classes.lean CoeDep}}
```
This is a chance to select only certain values, either by imposing further type class constraints on the value or by writing certain constructors directly.
For example, any `List` that is not actually empty can be coerced to a `NonEmptyList`:
```lean
{{#example_decl Examples/Classes.lean CoeDepListNEList}}
```

## Coercing to Types

In mathematics, it is common to have a concept that consists of a set equipped with additional structure.
For example, a monoid is some set _S_, an element _s_ of _S_, and an associative binary operator on _S_, such that _s_ is neutral on the left and right of the operator.
_S_ is referred to as the "carrier set" of the monoid.
The natural numbers with zero and addition form a monoid, for instance, because addition is associative and adding zero to any number is the identity.
Similarly, the natural numbers with one and multiplication also form a monoid.
Monoids are also widely used in functional programming: lists, the empty list, and the append operator form a monoid, as do strings, the empty string, and string append:
```lean
{{#example_decl Examples/Classes.lean Monoid}}
```
Given a monoid, it is possible to write the `foldMap` function that, in a single pass, transforms the entries in a list into a monoid's carrier set and then combines them using the monoid's operator.
Because monoids have a neutral element, there is a natural result to return when the list is empty, and because the operator is associative, clients of the function don't have to care whether the recursive function combines elements from left to right or from right to left.
```lean
{{#example_decl Examples/Classes.lean firstFoldMap}}
```

Even though a monoid consists of three separate pieces of information, it is common to just refer to the monoid's name in order to refer to its set.
Instead of saying "Let A be a monoid and let _x_ and _y_ be elements of its carrier set", it is common to say "Let _A_ be a monoid and let _x_ and _y_ be elements of _A_".
This practice can be encoded in Lean by defining a new kind of coercion, from the monoid to its carrier set.

The `CoeSort` class is just like the `Coe` class, with the exception that the target of the coercion must be a _sort_, namely `Type` or `Prop`.
The term _sort_ in Lean refers to these types that classify other types—`Type` classifies types that themselves classify data, and `Prop` classifies propositions that themselves classify evidence of their truth.
Just as `Coe` is checked when a type mismatch occurs, `CoeSort` is used when something other than a sort is provided in a context where a sort would be expected.

The coercion from a monoid into its carrier set extracts the carrier:
```lean
{{#example_decl Examples/Classes.lean CoeMonoid}}
```
With this coercion, the type signatures become less bureaucratic:
```lean
{{#example_decl Examples/Classes.lean foldMap}}
```

Most Lean programs do not implement new instances of `CoeSort`, especially when they are not working with algebraic structures.
However, as described in [the section on polymorphism](../getting-to-know/polymorphism.md), it occurs in error messages when a type constructor like `List` is used without an argument:
```lean
{{#example_in Examples/Classes.lean notAType2}}
```
```output error
{{#example_out Examples/Classes.lean notAType2}}
```
Additionally, it can occur when a non-type is used in a context where a type is expected:
```lean
{{#example_in Examples/Classes.lean notAType}}
```
```output error
{{#example_out Examples/Classes.lean notAType}}
```
These errors occur because Lean tries and fails to find a way to coerce these non-types into types.

## Coercing to Functions

Many datatypes that occur regularly in programming consist of a function along with some extra information about it.
For example, a function might be accompanied by a name to show in logs or by some configuration data.
Additionally, putting a type in a field of a structure, similarly to the `Monoid` example, can make sense in contexts where there are more than one way to implement an operation and more manual control is needed than type classes would allow.
For example, the specific details of values emitted by a JSON serializer may be important because another application expects a particular format.
Sometimes, the function itself may be derivable from just the configuration data.

A type class called `CoeFun` can transform values from non-function types to function types.
`CoeFun` has two parameters: the first is the type whose values should be transformed into functions, and the second is an output parameter that determines exactly which function type is being targeted.
```lean
{{#example_decl Examples/Classes.lean CoeFun}}
```
The second parameter is itself a function that computes a type.
In Lean, types are first-class and can be passed to functions or returned from them, just like anything else.


For example, a function that adds a constant amount to its argument can be represented as

For example, given the following representation of JSON values:
```lean
{{#example_decl Examples/Classes.lean JSON}}
```
a JSON serializer is a structure that tracks the type it knows how to serialize along with the serialization code itself:
```lean
{{#example_decl Examples/Classes.lean Serializer}}
```

## Messages You May Meet

Natural number literals are overloaded with the `OfNat` type class.
Because coercions fire in cases where types don't match, rather than in cases of missing instances, a missing `OfNat` instance for a type does not cause a coercion from `Nat` to be applied:
```lean
{{#example_in Examples/Classes.lean ofNatBeforeCoe}}
```
```output error
{{#example_out Examples/Classes.lean ofNatBeforeCoe}}
```

## Design Considerations

Coercions are a powerful tool that should be used responsibly.
On the one hand, they can allow an API to naturally follow the everyday rules of the domain being modeled.
This can be the difference between a bureaucratic mess of manual conversion functions and a clear program.
As Abelson and Sussman wrote in the preface to _Structure and Interpretation of Computer Programs_ (MIT Press, 1996),

> Programs must be written for people to read, and only incidentally for machines to execute.

Coercions, used wisely, are a valuable means of achieving readable code that can serve as the basis for communication with domain experts.

APIs that rely heavily on coercions have a number of important limitations, however.
Think carefully about these limitations before using coercions in your own libraries.

First off,coercions are only applied in contexts where enough type information is available for Lean to know all of the types involved, because there are no output parameters in the coercion type classes. This means that a return type annotation on a function can be the difference between a type error and a successfully applied coercion.
For example, the coercion from non-empty lists to lists makes the following program work:
```lean
{{#example_decl Examples/Classes.lean lastSpiderA}}
```
On the other hand, if the type annotation is omitted, then the result type is unknown, so Lean is unable to find the coercion:
```lean
{{#example_in Examples/Classes.lean lastSpiderB}}
```
```output error
{{#example_out Examples/Classes.lean lastSpiderB}}
```
More generally, when a coercion is not applied for some reason, the user receives the original type error, which can make it difficult to debug chains of coercions.

Finally, coercions are not applied in the context of field accessor notation.
This means that there is still an important difference between expressions that need to be coerced and those that don't, and this difference is visible to users of your API.

