

Outline:

 * Simple polymorphic types a la ML, relate `Point` to `Prod`/`MProd`
 * Recursive functions over `List`, with pattern matching
 * User-defined polymorphic datatypes (in the ML-typable fragment)
 * `Unit`, `Option`, `Sum`

Just as in most languages, types in Lean can take arguments.
For instance, the type `List Nat` describes lists of natural numbers, `List String` describes lists of strings, and `List (List Point)` describes lists of lists of points.
This is very similar to `List<Nat>`, `List<String>`, or `List<List<Point>>` in a language like C# or Java.
Just as Lean uses a space to pass an argument to a function, it uses a space to pass an argument to a type.

In functional programming, the term _polymorphism_ typically refers to datatypes and definitions that can be instantiated at multiple types.
This is different from the object-oriented programming community, where the term typically refers to subclasses that may override some behavior of their superclass.
In this book, "polymorphism" always refers to the first sense of the word.

The `Point` structure requires that both the `x` and `y` fields are `Float`s.
There is, however, nothing about points that require a specific representation for each coordinate.
A polymorphic version of `Point`, called `PPoint`, can take a type as an argument, and then use that type for both fields:
```Lean
{{#example_decl Examples/Intro.lean PPoint}}
```
Just as a function definition's arguments are written immediately after the name being defined, a structure's arguments are written immediately after the structure's name.
It is customary to use Greek letters to name type arguments in Lean when no more specific name suggests itself.
`Type` is a type that describes other types, so `Nat`, `List String`, and `PPoint Int` all have type `Type`.

Just like `List`, `PPoint` can be used by providing a specific type as its argument:
```Lean
{{#example_decl Examples/Intro.lean natPoint}}
```
In this example, both fields are expected to be `Nat`s.
Just as a function is called by replacing its argument variables with its argument values, providing `PPoint` with the type `Nat` as an argument yields a structure in which the fields `x` and `y` should have the type `Nat`, because the argument name `α` has been replaced by the argument type `Nat`.

Definitions may also take types as arguments, which makes them polymorphic.
While some languages have separate notations for type arguments and other arguments, Lean uses a single uniform notation for all arguments.
The function `replaceX` replaces the `x` field of a `PPoint` with a new value.
In order to allow `replaceX` to work with _any_ polymorphic point, it must be polymorphic itself.
This is achieved by having its first argument be the type of the point's fields, and later arguments refer back to the first argument's name.
```Lean
{{#example_decl Examples/Intro.lean replaceX}}
```
In other words, when the types of the arguments `point` and `newX` mention `α`, they are referring to _whichever type was provided as the first argument_.
This is similar to the way that function argument names refer to the values that were provided when they occur in the function's body.

This can be seen by asking Lean to check the type of `replaceX`, and then asking it to check the type of `replaceX Nat`.
```Lean
{{#example_in Examples/Intro.lean replaceXT}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXT}}
```
This function type includes the _name_ of the first argument, and later arguments in the type refer back to this name.
Just as the value of a function application is found by replacing the argument name with the provided argument value in the function's body, the type of a function application is found by replacing the argument's name with the provided value in the function's return type.
Providing the first argument, `Nat`, causes all occurrences of `α` in the remainder of the type to be replaced with `Nat`:
```Lean
{{#example_in Examples/Intro.lean replaceXNatT}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXNatT}}
```
Because the remaining arguments are not explicitly named, no further substitution occurs as more arguments are provided:
```Lean
{{#example_in Examples/Intro.lean replaceXNatOriginT}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXNatOriginT}}
```
```Lean
{{#example_in Examples/Intro.lean replaceXNatOriginFiveT}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXNatOriginFiveT}}
```
The fact that the type of the whole function application expression was determined by passing a type as an argument has no bearing on the ability to evaluate it.
```Lean
{{#example_in Examples/Intro.lean replaceXNatOriginFiveV}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXNatOriginFiveV}}
```

# Linked Lists

Lean's standard library includes a canonical linked list datatype, called `List`, and special syntax that makes it more convenient to use.
Lists are written in square brackets.
For instance, a list that contains the prime numbers less than 10 can be written:
```Lean
{{#example_decl Examples/Intro.lean primesUnder10}}
```

Behind the scenes, `List` is an inductive datatype, defined like this:
```Lean
{{#example_decl Examples/Intro.lean List}}
```
The actual definition in the standard library is slightly different, because it uses features that have not yet been presented.
This definition says that `List` takes a single type as its argument, just as `PPoint` did.
According to the constructors, a `List α` can be built with either `nil` or `cons`.
The constructor `nil` represents empty lists, and the constructor `cons` represents a single element in the linked list.
The first argument to `cons` is the head of the list, and the second argument is its tail.

The `primesUnder10` example can be written more explicitly by using `List`'s constructors directly:
```Lean
{{#example_decl Examples/Intro.lean explicitPrimesUnder10}}
```
These two definitions are completely equivalent, but `primesUnder10` is much easier to read than `explicitPrimesUnder10`.

Functions that consume `List`s can be defined in much the same way as functions that consume `Nat`s.
Indeed, one way to think of a linked list is as a `Nat` that has an extra data field dangling off each `succ` constructor.




# Messages You May Meet


Type : Type
