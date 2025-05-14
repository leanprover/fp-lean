import VersoManual
import FPLean.Examples

open Verso.Genre Manual ExternalLean

open FPLean

example_module Examples.Intro

#doc (Manual) "Functions and Definitions" =>

:::paragraph
In Lean, definitions are introduced using the {kw}`def` keyword.
For instance, to define the name {exampleIn}`helloNameVal` to refer to the string {exampleOut}`helloNameVal`, write:

{exampleDecl hello}

In Lean, new names are defined using the colon-equal operator `:=` rather than `=`.
This is because `=` is used to describe equalities between existing expressions, and using two different operators helps prevent confusion.
:::

:::paragraph
In the definition of {exampleIn}`helloNameVal`, the expression {exampleOut}`helloNameVal` is simple enough that Lean is able to determine the definition's type automatically.
However, most definitions are not so simple, so it will usually be necessary to add a type.
This is done using a colon after the name being defined.

{exampleDecl lean}

:::

:::paragraph
Now that the names have been defined, they can be used, so

{exampleIn helloLean}

outputs

{exampleInfo helloLean}

In Lean, defined names may only be used after their definitions.
:::

In many languages, definitions of functions use a different syntax than definitions of other values.
For instance, Python function definitions begin with the {kw}`def` keyword, while other definitions are defined with an equals sign.
In Lean, functions are defined using the same {kw}`def` keyword as other values.
Nonetheless, definitions such as {exampleIn}`helloNameVal` introduce names that refer _directly_ to their values, rather than to zero-argument functions that return equivalent results each time they are called.

# Defining Functions

:::paragraph
There are a variety of ways to define functions in Lean. The simplest is to place the function's arguments before the definition's type, separated by spaces. For instance, a function that adds one to its argument can be written:

{exampleDecl add1}

Testing this function with {kw}`#eval` gives {exampleInfo}`add1_7`, as expected:

{exampleIn add1_7}

:::

:::paragraph
Just as functions are applied to multiple arguments by writing spaces between each argument, functions that accept multiple arguments are defined with spaces between the arguments' names and types. The function {term}`maximum.name`, whose result is equal to the greatest of its two arguments, takes two {term}`Nat.name` arguments {term}`maximum.n` and {term}`maximum.k` and returns a {term}`Nat.name`.

{exampleDecl maximum}

Similarly, the function {term}`spaceBetween.name` joins two strings with a space between them.

{exampleDecl spaceBetween}

:::

:::paragraph
When a defined function like {term}`maximum.name` has been provided with its arguments, the result is determined by first replacing the argument names with the provided values in the body, and then evaluating the resulting body. For example:

{exampleEval maximum_eval}

:::

Expressions that evaluate to natural numbers, integers, and strings have types that say this ({term}`Nat.name`, {term}`Int.name`, and {term}`String.name`, respectively).
This is also true of functions.
A function that accepts a {term}`Nat.name` and returns a {term}`Bool.name` has type {term}`Nat→Bool`, and a function that accepts two {term}`Nat.name`s and returns a {term}`Nat.name` has type {term}`Nat→Nat→Nat`.

As a special case, Lean returns a function's signature when its name is used directly with {kw}`#check`.
Entering {exampleIn}`add1sig` yields {exampleInfo}`add1sig`.
However, Lean can be “tricked” into showing the function's type by writing the function's name in parentheses, which causes the function to be treated as an ordinary expression, so {exampleIn}`add1type` yields {exampleInfo}`add1type` and {exampleIn}`maximumType` yields {exampleInfo}`maximumType`.
This arrow can also be written with an ASCII alternative arrow `->`, so the preceding function types can be written {exampleOut}`add1typeASCII` and {exampleOut}`maximumTypeASCII`, respectively.

Behind the scenes, all functions actually expect precisely one argument.
Functions like {term}`maximum.name` that seem to take more than one argument are in fact functions that take one argument and then return a new function.
This new function takes the next argument, and the process continues until no more arguments are expected.
This can be seen by providing one argument to a multiple-argument function: {exampleIn}`maximum3Type` yields {exampleInfo}`maximum3Type` and {exampleIn}`stringAppendHelloType` yields {exampleInfo}`stringAppendHelloType`.
Using a function that returns a function to implement multiple-argument functions is called _currying_ after the mathematician Haskell Curry.
Function arrows associate to the right, which means that {term}`Nat→Nat→Nat` should be parenthesized {term}`Nat→(Nat→Nat)`.

## Exercises

 * Define the function {term}`joinStringsWith.name` with type {term}`joinStringsWith.type` that creates a new string by placing its first argument between its second and third arguments. {exampleEval 0}`joinStringsWithEx` should evaluate to {exampleEval 1}`joinStringsWithEx`.
 * What is the type of {term}`joinStringsWith.name`? Check your answer with Lean.
 * Define a function {term}`volume.name` with type {term}`volume.type` that computes the volume of a rectangular prism with the given height, width, and depth.

# Defining Types

Most typed programming languages have some means of defining aliases for types, such as C's `typedef`.
In Lean, however, types are a first-class part of the language—they are expressions like any other.
This means that definitions can refer to types just as well as they can refer to other values.

:::paragraph
For example, if {term}`String.name` is too much to type, a shorter abbreviation {term}``Str.name`` can be defined:

{exampleDecl StringTypeDef}

It is then possible to use {term}``Str.name`` as a definition's type instead of {term}``String.name``:

{exampleDecl aStr}

:::

The reason this works is that types follow the same rules as the rest of Lean.
Types are expressions, and in an expression, a defined name can be replaced with its definition.
Because {term}``Str.name`` has been defined to mean {term}``String.name``, the definition of {term}``aStr.name`` makes sense.

## Messages You May Meet

:::paragraph
Experimenting with using definitions for types is made more complicated by the way that Lean supports overloaded integer literals.
If {term}``Nat.name`` is too short, a longer name {term}``NaturalNumber`` can be defined:

{exampleDecl NaturalNumberTypeDef}

However, using {term}``NaturalNumber`` as a definition's type instead of {term}``Nat.name`` does not have the expected effect.
In particular, the definition:

{exampleIn thirtyEight}

results in the following error:

{exampleError thirtyEight}

:::

This error occurs because Lean allows number literals to be _overloaded_.
When it makes sense to do so, natural number literals can be used for new types, just as if those types were built in to the system.
This is part of Lean's mission of making it convenient to represent mathematics, and different branches of mathematics use number notation for very different purposes.
The specific feature that allows this overloading does not replace all defined names with their definitions before looking for overloading, which is what leads to the error message above.

One way to work around this limitation is by providing the type {term}`Nat.name` on the right-hand side of the definition, causing {term}`Nat.name`'s overloading rules to be used for {term}`thirtyEightFixed.val`:

{exampleDecl thirtyEightFixed}

The definition is still type-correct because {exampleEval 0}`NaturalNumberDef` is the same type as {exampleEval 1}`NaturalNumberDef`—by definition!

Another solution is to define an overloading for {term}`NaturalNumber` that works equivalently to the one for {term}`Nat.name`.
This requires more advanced features of Lean, however.

:::paragraph
Finally, defining the new name for {term}`Nat.name` using {kw}`abbrev` instead of {kw}`def` allows overloading resolution to replace the defined name with its definition.
Definitions written using {kw}`abbrev` are always unfolded.
For instance,

{exampleDecl NTypeDef}

and

{exampleDecl thirtyNine}

are accepted without issue.
:::

Behind the scenes, some definitions are internally marked as being unfoldable during overload resolution, while others are not.
Definitions that are to be unfolded are called _reducible_.
Control over reducibility is essential to allow Lean to scale: fully unfolding all definitions can result in very large types that are slow for a machine to process and difficult for users to understand.
Definitions produced with {kw}`abbrev` are marked as reducible.
