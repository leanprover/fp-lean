In Lean, definitions are introduced using the `def` keyword. For instance, to define the name `{{#example_in Examples/Intro.lean helloNameVal}}` to refer to the string `{{#example_out Examples/Intro.lean helloNameVal}}`, write:

```Lean
{{#example_decl Examples/Intro.lean hello}}
```

In Lean, new names are defined using the colon-equal operator`:=`
rather than `=`. This is because `=` is used to describe equalities
between existing expressions, and using two different operators helps
keep these usages different.

In the definition of `{{#example_in Examples/Intro.lean helloNameVal}}`,
`{{#example_out Examples/Intro.lean helloNameVal}}` is simple enough
that Lean is able to determine the definition's type automatically. However,
most definitions are not so simple, so it will usually be necessary to add a
type. This is done using a colon after the name being defined.

```Lean
{{#example_decl Examples/Intro.lean lean}}
```

Now that the names have been defined, they can be used, so
``` Lean
{{#example_in Examples/Intro.lean helloLean}}
```
outputs
``` Lean
{{#example_out Examples/Intro.lean helloLean}}
```

In Lean, defined names may only be used after their definitions.

# Defining Functions

There are a variety of ways to define functions. The simplest is to place the function's arguments before the definition's type. For instance, a function that adds one to its argument can be written:

```Lean
{{#example_decl Examples/Intro.lean add1}}
```

Testing this function with `#eval` gives `{{#example_out Examples/Intro.lean add1_7}}`, as expected:
```Lean
{{#example_in Examples/Intro.lean add1_7}}
```


Just as functions are applied to multiple arguments just by writing spaces between each argument, functions that accept multiple arguments are defined with spaces between the arguments' names and types. The function `maximum`, whose result is equal to the greatest of its two arguments, takes two `Nat` arguments `n` and `k` and returns a `Nat`.

```Lean
{{#example_decl Examples/Intro.lean maximum}}
```

When a defined function like `maximum` has been provided with its arguments, the result is determined by first replacing the argument names with the provided values in the body, and then evaluating the resulting body. For example:
```Lean
{{#example_eval Examples/Intro.lean maximum_eval}}
```

Expressions that evaluate to natural numbers, integers, and strings have types that say this (`Nat`, `Int`, and `String`, respectively). This is also true of functions. A function that accepts a `Nat` and returns a `Bool` has type `Nat → Bool`, and a function that accepts two `Nat`s and returns a `Nat` has type `Nat → Nat → Nat`. This arrow can also be written with an ASCII alternative arrow `->`, so the preceding function types can be written `Nat -> Bool` and `Nat -> Nat -> Nat`, respectively.
Entering `{{#example_in Examples/Intro.lean add1type}}` yields `{{#example_out Examples/Intro.lean add1type}}`
and `{{#example_in Examples/Intro.lean maximumType}}` yields `{{#example_out Examples/Intro.lean maximumType}}`.

Behind the scenes, all functions actually expect precisely one argument. Functions like `maximum` that seem to take more than one argument are in fact functions that take one argument and then return a new function. This new function takes the next argument, and the process continues until there are no more arguments. This can be seen by providing one argument to a multi-argument function: `{{#example_in Examples/Intro.lean maximum3Type}}` yields `{{#example_out Examples/Intro.lean maximum3Type}}` and `{{#example_in Examples/Intro.lean stringAppendHelloType}}` yields `{{#example_out Examples/Intro.lean stringAppendHelloType}}`.

## Exercises

 * Define the function `joinStringsWith` with type `String -> String -> String -> String` that creates a new string by placing its first argument between its second and third arguments. `{{#example_eval Examples/Intro.lean joinStringsWithEx 0}}` should evaluate to `{{#example_eval Examples/Intro.lean joinStringsWithEx 1}}`.
 * What is the type of `joinStringsWith ": "`? Check your answer with Lean.
 * Define a function `volume` with type `Nat → Nat → Nat → Nat` that computes the volume of a rectangular prism with the given height, width, and depth.







