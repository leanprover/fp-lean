# Functions and Definitions

In Lean, definitions are introduced using the `def` keyword. For instance, to define the name `{{#example_in Examples/Intro.lean helloNameVal}}` to refer to the string `{{#example_out Examples/Intro.lean helloNameVal}}`, write:

```lean
{{#example_decl Examples/Intro.lean hello}}
```

In Lean, new names are defined using the colon-equal operator`:=`
rather than `=`. This is because `=` is used to describe equalities
between existing expressions, and using two different operators helps
prevent confusion.

In the definition of `{{#example_in Examples/Intro.lean helloNameVal}}`, the expression `{{#example_out Examples/Intro.lean helloNameVal}}` is simple enough that Lean is able to determine the definition's type automatically.
However, most definitions are not so simple, so it will usually be necessary to add a type.
This is done using a colon after the name being defined.

```lean
{{#example_decl Examples/Intro.lean lean}}
```

Now that the names have been defined, they can be used, so
``` Lean
{{#example_in Examples/Intro.lean helloLean}}
```
outputs
``` Lean info
{{#example_out Examples/Intro.lean helloLean}}
```
In Lean, defined names may only be used after their definitions.

In many languages, definitions of functions use a different syntax than definitions of other values.
For instance, Python function definitions begin with the `def` keyword, while other definitions are defined with an equals sign.
In Lean, functions are defined using the same `def` keyword as other values.
Nonetheless, definitions such as `hello` introduce names that refer _directly_ to their values, rather than to zero-argument functions that return equivalent results each time they are called.

## Defining Functions

There are a variety of ways to define functions in Lean. The simplest is to place the function's arguments before the definition's type, separated by spaces. For instance, a function that adds one to its argument can be written:

```lean
{{#example_decl Examples/Intro.lean add1}}
```

Testing this function with `#eval` gives `{{#example_out Examples/Intro.lean add1_7}}`, as expected:
```lean
{{#example_in Examples/Intro.lean add1_7}}
```


Just as functions are applied to multiple arguments by writing spaces between each argument, functions that accept multiple arguments are defined with spaces between the arguments' names and types. The function `maximum`, whose result is equal to the greatest of its two arguments, takes two `Nat` arguments `n` and `k` and returns a `Nat`.

```lean
{{#example_decl Examples/Intro.lean maximum}}
```

Similarly, the function `spaceBetween` joins two strings with a space between them.

```lean
{{#example_decl Examples/Intro.lean spaceBetween}}
```

When a defined function like `maximum` has been provided with its arguments, the result is determined by first replacing the argument names with the provided values in the body, and then evaluating the resulting body. For example:
```lean
{{#example_eval Examples/Intro.lean maximum_eval}}
```

Expressions that evaluate to natural numbers, integers, and strings have types that say this (`Nat`, `Int`, and `String`, respectively).
This is also true of functions.
A function that accepts a `Nat` and returns a `Bool` has type `Nat → Bool`, and a function that accepts two `Nat`s and returns a `Nat` has type `Nat → Nat → Nat`.

As a special case, Lean returns a function's signature when its name is used directly with `#check`.
Entering `{{#example_in Examples/Intro.lean add1sig}}` yields `{{#example_out Examples/Intro.lean add1sig}}`.
However, Lean can be "tricked" into showing the function's type by writing the function's name in parentheses, which causes the function to be treated as an ordinary expression, so `{{#example_in Examples/Intro.lean add1type}}` yields `{{#example_out Examples/Intro.lean add1type}}` and `{{#example_in Examples/Intro.lean maximumType}}` yields `{{#example_out Examples/Intro.lean maximumType}}`.
This arrow can also be written with an ASCII alternative arrow `->`, so the preceding function types can be written `{{#example_out Examples/Intro.lean add1typeASCII}}` and `{{#example_out Examples/Intro.lean maximumTypeASCII}}`, respectively.

Behind the scenes, all functions actually expect precisely one argument.
Functions like `maximum` that seem to take more than one argument are in fact functions that take one argument and then return a new function.
This new function takes the next argument, and the process continues until no more arguments are expected.
This can be seen by providing one argument to a multiple-argument function: `{{#example_in Examples/Intro.lean maximum3Type}}` yields `{{#example_out Examples/Intro.lean maximum3Type}}` and `{{#example_in Examples/Intro.lean stringAppendHelloType}}` yields `{{#example_out Examples/Intro.lean stringAppendHelloType}}`.
Using a function that returns a function to implement multiple-argument functions is called _currying_ after the mathematician Haskell Curry.
Function arrows associate to the right, which means that `Nat → Nat → Nat` should be parenthesized `Nat → (Nat → Nat)`.

### Exercises

 * Define the function `joinStringsWith` with type `String -> String -> String -> String` that creates a new string by placing its first argument between its second and third arguments. `{{#example_eval Examples/Intro.lean joinStringsWithEx 0}}` should evaluate to `{{#example_eval Examples/Intro.lean joinStringsWithEx 1}}`.
 * What is the type of `joinStringsWith ": "`? Check your answer with Lean.
 * Define a function `volume` with type `Nat → Nat → Nat → Nat` that computes the volume of a rectangular prism with the given height, width, and depth.

## Defining Types

Most typed programming languages have some means of defining aliases for types, such as C's `typedef`.
In Lean, however, types are a first-class part of the language - they are expressions like any other.
This means that definitions can refer to types just as well as they can refer to other values.

For example, if ``String`` is too much to type, a shorter abbreviation ``Str`` can be defined:
```lean
{{#example_decl Examples/Intro.lean StringTypeDef}}
```
It is then possible to use ``Str`` as a definition's type instead of ``String``:
```lean
{{#example_decl Examples/Intro.lean aStr}}
```

The reason this works is that types follow the same rules as the rest of Lean.
Types are expressions, and in an expression, a defined name can be replaced with its definition.
Because ``Str`` has been defined to mean ``String``, the definition of ``aStr`` makes sense.

### Messages You May Meet

Experimenting with using definitions for types is made more complicated by the way that Lean supports overloaded integer literals.
If ``Nat`` is too short, a longer name ``NaturalNumber`` can be defined:
```lean
{{#example_decl Examples/Intro.lean NaturalNumberTypeDef}}
```
However, using ``NaturalNumber`` as a definition's type instead of ``Nat`` does not have the expected effect.
In particular, the definition:
```lean
{{#example_in Examples/Intro.lean thirtyEight}}
```
results in the following error:
```output error
{{#example_out Examples/Intro.lean thirtyEight}}
```

This error occurs because Lean allows number literals to be _overloaded_.
When it makes sense to do so, natural number literals can be used for new types, just as if those types were built in to the system.
This is part of Lean's mission of making it convenient to represent mathematics, and different branches of mathematics use number notation for very different purposes.
The specific feature that allows this overloading does not replace all defined names with their definitions before looking for overloading, which is what leads to the error message above.

One way to work around this limitation is by providing the type `Nat` on the right-hand side of the definition, causing `Nat`'s overloading rules to be used for `38`:
```lean
{{#example_decl Examples/Intro.lean thirtyEightFixed}}
```
The definition is still type-correct because `{{#example_eval Examples/Intro.lean NaturalNumberDef 0}}` is the same type as `{{#example_eval Examples/Intro.lean NaturalNumberDef 1}}`—by definition!

Another solution is to define an overloading for `NaturalNumber` that works equivalently to the one for `Nat`.
This requires more advanced features of Lean, however.

Finally, defining the new name for `Nat` using `abbrev` instead of `def` allows overloading resolution to replace the defined name with its definition.
Definitions written using `abbrev` are always unfolded.
For instance,
```lean
{{#example_decl Examples/Intro.lean NTypeDef}}
```
and
```lean
{{#example_decl Examples/Intro.lean thirtyNine}}
```
are accepted without issue.

Behind the scenes, some definitions are internally marked as being unfoldable during overload resolution, while others are not.
Definitions that are to be unfolded are called _reducible_.
Control over reducibility is essential to allow Lean to scale: fully unfolding all definitions can result in very large types that are slow for a machine to process and difficult for users to understand.
Definitions produced with `abbrev` are marked as reducible.
