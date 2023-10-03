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
The function `Pos.toNat` that was defined earlier converts a `Pos` to the corresponding `Nat`:
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
Because the author of `List.drop` did not make it a method of a type class, it can't be overridden by defining a new instance.

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

## Chaining Coercions

When searching for coercions, Lean will attempt to assemble a coercion out of a chain of smaller coercions.
For example, there is already a coercion from `Nat` to `Int`.
Because of that instance, combined with the `Coe Pos Nat` instance, the following code is accepted:
```lean
{{#example_decl Examples/Classes.lean posInt}}
```
This definition uses two coercions: from `Pos` to `Nat`, and then from `Nat` to `Int`.

The Lean compiler does not get stuck in the presence of circular coercions.
For example, even if two types `A` and `B` can be coerced to one another, their mutual coercions can be used to find a path:
```lean
{{#example_decl Examples/Classes.lean CoercionCycle}}
```
Remember: the double parentheses `()` is short for the constructor `Unit.unit`.
After deriving a `Repr B` instance,
```lean
{{#example_in Examples/Classes.lean coercedToBEval}}
```
results in:
```output info
{{#example_out Examples/Classes.lean coercedToBEval}}
```

The `Option` type can be used similarly to nullable types in C# and Kotlin: the `none` constructor represents the absence of a value.
The Lean standard library defines a coercion from any type `α` to `Option α` that wraps the value in `some`.
This allows option types to be used in a manner even more similar to nullable types, because `some` can be omitted.
For instance, the function `List.getLast?` that finds the last entry in a list can be written without a `some` around the return value `x`:
```lean
{{#example_decl Examples/Classes.lean lastHuh}}
```
Instance search finds the coercion, and inserts a call to `coe`, which wraps the argument in `some`.
These coercions can be chained, so that nested uses of `Option` don't require nested `some` constructors:
```lean
{{#example_decl Examples/Classes.lean perhapsPerhapsPerhaps}}
```

Coercions are only activated automatically when Lean encounters a mismatch between an inferred type and a type that is imposed from the rest of the program.
In cases with other errors, coercions are not activated.
For example, if the error is that an instance is missing, coercions will not be used:
```lean
{{#example_in Examples/Classes.lean ofNatBeforeCoe}}
```
```output error
{{#example_out Examples/Classes.lean ofNatBeforeCoe}}
```

This can be worked around by manually indicating the desired type to be used for `OfNat`:
```lean
{{#example_decl Examples/Classes.lean perhapsPerhapsPerhapsNat}}
```
Additionally, coercions can be manually inserted using an up arrow:
```lean
{{#example_decl Examples/Classes.lean perhapsPerhapsPerhapsNatUp}}
```
In some cases, this can be used to ensure that Lean finds the right instances.
It can also make the programmer's intentions more clear.


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
The natural numbers with zero and addition form a monoid, because addition is associative and adding zero to any number is the identity.
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

Another useful example of `CoeSort` is used to bridge the gap between `Bool` and `Prop`.
As discussed in [the section on ordering and equality](standard-classes.md#equality-and-ordering), Lean's `if` expression expects the condition to be a decidable proposition rather than a `Bool`.
Programs typically need to be able to branch based on Boolean values, however.
Rather than have two kinds of `if` expression, the Lean standard library defines a coercion from `Bool` to the proposition that the `Bool` in question is equal to `true`:
```lean
{{#example_decl Examples/Classes.lean CoeBoolProp}}
```
In this case, the sort in question is `Prop` rather than `Type`.

## Coercing to Functions

Many datatypes that occur regularly in programming consist of a function along with some extra information about it.
For example, a function might be accompanied by a name to show in logs or by some configuration data.
Additionally, putting a type in a field of a structure, similarly to the `Monoid` example, can make sense in contexts where there is more than one way to implement an operation and more manual control is needed than type classes would allow.
For example, the specific details of values emitted by a JSON serializer may be important because another application expects a particular format.
Sometimes, the function itself may be derivable from just the configuration data.

A type class called `CoeFun` can transform values from non-function types to function types.
`CoeFun` has two parameters: the first is the type whose values should be transformed into functions, and the second is an output parameter that determines exactly which function type is being targeted.
```lean
{{#example_decl Examples/Classes.lean CoeFun}}
```
The second parameter is itself a function that computes a type.
In Lean, types are first-class and can be passed to functions or returned from them, just like anything else.

For example, a function that adds a constant amount to its argument can be represented as a wrapper around the amount to add, rather than by defining an actual function:
```lean
{{#example_decl Examples/Classes.lean Adder}}
```
A function that adds five to its argument has a `5` in the `howMuch` field:
```lean
{{#example_decl Examples/Classes.lean add5}}
```
This `Adder` type is not a function, and applying it to an argument results in an error:
```lean
{{#example_in Examples/Classes.lean add5notfun}}
```
```output error
{{#example_out Examples/Classes.lean add5notfun}}
```
Defining a `CoeFun` instance causes Lean to transform the adder into a function with type `Nat → Nat`:
```lean
{{#example_decl Examples/Classes.lean CoeFunAdder}}

{{#example_in Examples/Classes.lean add53}}
```
```output info
{{#example_out Examples/Classes.lean add53}}
```
Because all `Adder`s should be transformed into `Nat → Nat` functions, the argument to `CoeFun`'s second parameter was ignored.

When the value itself is needed to determine the right function type, then `CoeFun`'s second parameter is no longer ignored.
For example, given the following representation of JSON values:
```lean
{{#example_decl Examples/Classes.lean JSON}}
```
a JSON serializer is a structure that tracks the type it knows how to serialize along with the serialization code itself:
```lean
{{#example_decl Examples/Classes.lean Serializer}}
```
A serializer for strings need only wrap the provided string in the `JSON.string` constructor:
```lean
{{#example_decl Examples/Classes.lean StrSer}}
```
Viewing JSON serializers as functions that serialize their argument requires extracting the inner type of serializable data:
```lean
{{#example_decl Examples/Classes.lean CoeFunSer}}
```
Given this instance, a serializer can be applied directly to an argument:
```lean
{{#example_decl Examples/Classes.lean buildResponse}}
```
The serializer can be passed directly to `buildResponse`:
```lean
{{#example_in Examples/Classes.lean buildResponseOut}}
```
```output info
{{#example_out Examples/Classes.lean buildResponseOut}}
```

### Aside: JSON as a String

It can be a bit difficult to understand JSON when encoded as Lean objects.
To help make sure that the serialized response was what was expected, it can be convenient to write a simple converter from `JSON` to `String`.
The first step is to simplify the display of numbers.
`JSON` doesn't distinguish between integers and floating point numbers, and the type `Float` is used to represent both.
In Lean, `Float.toString` includes a number of trailing zeros:
```lean
{{#example_in Examples/Classes.lean fiveZeros}}
```
```output info
{{#example_out Examples/Classes.lean fiveZeros}}
```
The solution is to write a little function that cleans up the presentation by dropping all trailing zeros, followed by a trailing decimal point:
```lean
{{#example_decl Examples/Classes.lean dropDecimals}}
```
With this definition, `{{#example_in Examples/Classes.lean dropDecimalExample}}` yields `{{#example_out Examples/Classes.lean dropDecimalExample}}`, and `{{#example_in Examples/Classes.lean dropDecimalExample2}}` yields `{{#example_out Examples/Classes.lean dropDecimalExample2}}`.

The next step is to define a helper function to append a list of strings with a separator in between them:
```lean
{{#example_decl Examples/Classes.lean Stringseparate}}
```
This function is useful to account for comma-separated elements in JSON arrays and objects.
`{{#example_in Examples/Classes.lean sep2ex}}` yields `{{#example_out Examples/Classes.lean sep2ex}}`, `{{#example_in Examples/Classes.lean sep1ex}}` yields `{{#example_out Examples/Classes.lean sep1ex}}`, and `{{#example_in Examples/Classes.lean sep0ex}}` yields `{{#example_out Examples/Classes.lean sep0ex}}`.

Finally, a string escaping procedure is needed for JSON strings, so that the Lean string containing `"Hello!"` can be output as `"\"Hello!\""`.
Fortunately, the Lean compiler contains an internal function for escaping JSON strings already, called `Lean.Json.escape`.
To access this function, add `import Lean` to the beginning of your file.

The function that emits a string from a `JSON` value is declared `partial` because Lean cannot see that it terminates.
This is because recursive calls to `asString` occur in functions that are being applied by `List.map`, and this pattern of recursion is complicated enough that Lean cannot see that the recursive calls are actually being performed on smaller values.
In an application that just needs to produce JSON strings and doesn't need to mathematically reason about the process, having the function be `partial` is not likely to cause problems.
```lean
{{#example_decl Examples/Classes.lean JSONasString}}
```
With this definition, the output of serialization is easier to read:
```lean
{{#example_in Examples/Classes.lean buildResponseStr}}
```
```output info
{{#example_out Examples/Classes.lean buildResponseStr}}
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

First off, coercions are only applied in contexts where enough type information is available for Lean to know all of the types involved, because there are no output parameters in the coercion type classes. This means that a return type annotation on a function can be the difference between a type error and a successfully applied coercion.
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



