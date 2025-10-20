import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "Functions and Definitions" =>
%%%
tag := "functions-and-definitions"
%%%

:::paragraph
In Lean, definitions are introduced using the {kw}`def` keyword.
For instance, to define the name {anchorTerm helloNameVal}`hello` to refer to the string {anchorTerm helloNameVal}`"Hello"`, write:

```anchor hello
def hello := "Hello"
```

In Lean, new names are defined using the colon-equal operator {anchorTerm hello}`:=` rather than {anchorTerm helloNameVal}`=`.
This is because {anchorTerm helloNameVal}`=` is used to describe equalities between existing expressions, and using two different operators helps prevent confusion.
:::

:::paragraph
In the definition of {anchorTerm helloNameVal}`hello`, the expression {anchorTerm helloNameVal}`"Hello"` is simple enough that Lean is able to determine the definition's type automatically.
However, most definitions are not so simple, so it will usually be necessary to add a type.
This is done using a colon after the name being defined:

```anchor lean
def lean : String := "Lean"
```

:::

:::paragraph
Now that the names have been defined, they can be used, so

```anchor helloLean
#eval String.append hello (String.append " " lean)
```

outputs

```anchorInfo helloLean
"Hello Lean"
```

In Lean, defined names may only be used after their definitions.
:::

In many languages, definitions of functions use a different syntax than definitions of other values.
For instance, Python function definitions begin with the {kw}`def` keyword, while other definitions are defined with an equals sign.
In Lean, functions are defined using the same {kw}`def` keyword as other values.
Nonetheless, definitions such as {anchorTerm helloNameVal}`hello` introduce names that refer _directly_ to their values, rather than to zero-argument functions that return equivalent results each time they are called.

# Defining Functions
%%%
tag := "defining-functions"
%%%

:::paragraph
There are a variety of ways to define functions in Lean. The simplest is to place the function's arguments before the definition's type, separated by spaces. For instance, a function that adds one to its argument can be written:

```anchor add1
def add1 (n : Nat) : Nat := n + 1
```

Testing this function with {kw}`#eval` gives {anchorInfo add1_7}`8`, as expected:

```anchor add1_7
#eval add1 7
```

:::

:::paragraph
Just as functions are applied to multiple arguments by writing spaces between each argument, functions that accept multiple arguments are defined with spaces between the arguments' names and types. The function {anchorName maximum}`maximum`, whose result is equal to the greatest of its two arguments, takes two {anchorName maximum}`Nat` arguments {anchorName Nat}`n` and {anchorName maximum}`k` and returns a {anchorName maximum}`Nat`.

```anchor maximum
def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n
```

Similarly, the function {anchorName spaceBetween}`spaceBetween` joins two strings with a space between them.

```anchor spaceBetween
def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)
```

:::

:::paragraph
When a defined function like {anchorName maximum_eval}`maximum` has been provided with its arguments, the result is determined by first replacing the argument names with the provided values in the body, and then evaluating the resulting body. For example:

```anchorEvalSteps maximum_eval
maximum (5 + 8) (2 * 7)
===>
maximum 13 14
===>
if 13 < 14 then 14 else 13
===>
14
```

:::

Expressions that evaluate to natural numbers, integers, and strings have types that say this ({anchorName Nat}`Nat`, {anchorName Positivity}`Int`, and {anchorName Book}`String`, respectively).
This is also true of functions.
A function that accepts a {anchorName Nat}`Nat` and returns a {anchorName Bool}`Bool` has type {anchorTerm evenFancy}`Nat → Bool`, and a function that accepts two {anchorName Nat}`Nat`s and returns a {anchorName Nat}`Nat` has type {anchorTerm currying}`Nat → Nat → Nat`.

As a special case, Lean returns a function's signature when its name is used directly with {kw}`#check`.
Entering {anchorTerm add1sig}`#check add1` yields {anchorInfo add1sig}`add1 (n : Nat) : Nat`.
However, Lean can be “tricked” into showing the function's type by writing the function's name in parentheses, which causes the function to be treated as an ordinary expression, so {anchorTerm add1type}`#check (add1)` yields {anchorInfo add1type}`add1 : Nat → Nat` and {anchorTerm maximumType}`#check (maximum)` yields {anchorInfo maximumType}`maximum : Nat → Nat → Nat`.
This arrow can also be written with an ASCII alternative arrow {anchorTerm add1typeASCII}`->`, so the preceding function types can be written {anchorTerm add1typeASCII}`example : Nat -> Nat := add1` and {anchorTerm maximumTypeASCII}`example : Nat -> Nat -> Nat := maximum`, respectively.

Behind the scenes, all functions actually expect precisely one argument.
Functions like {anchorName maximum3Type}`maximum` that seem to take more than one argument are in fact functions that take one argument and then return a new function.
This new function takes the next argument, and the process continues until no more arguments are expected.
This can be seen by providing one argument to a multiple-argument function: {anchorTerm maximum3Type}`#check maximum 3` yields {anchorInfo maximum3Type}`maximum 3 : Nat → Nat` and {anchorTerm stringAppendHelloType}`#check spaceBetween "Hello "` yields {anchorInfo stringAppendHelloType}`spaceBetween "Hello " : String → String`.
Using a function that returns a function to implement multiple-argument functions is called _currying_ after the mathematician Haskell Curry.
Function arrows associate to the right, which means that {anchorTerm currying}`Nat → Nat → Nat` should be parenthesized {anchorTerm currying}`Nat → (Nat → Nat)`.

## Exercises
%%%
tag := "function-definition-exercises"
%%%

 * Define the function {anchorName joinStringsWithEx}`joinStringsWith` with type {anchorTerm joinStringsWith}`String → String → String → String` that creates a new string by placing its first argument between its second and third arguments. {anchorEvalStep joinStringsWithEx 0}`joinStringsWith ", " "one" "and another"` should evaluate to {anchorEvalStep joinStringsWithEx 1}`"one, and another"`.
 * What is the type of {anchorTerm joinStringsWith}`joinStringsWith ": "`? Check your answer with Lean.
 * Define a function {anchorName volume}`volume` with type {anchorTerm volume}`Nat → Nat → Nat → Nat` that computes the volume of a rectangular prism with the given height, width, and depth.

# Defining Types
%%%
tag := "defining-types"
%%%

Most typed programming languages have some means of defining aliases for types, such as C's {c}`typedef`.
In Lean, however, types are a first-class part of the language—they are expressions like any other.
This means that definitions can refer to types just as well as they can refer to other values.

:::paragraph
For example, if {anchorName StringTypeDef}`String` is too much to type, a shorter abbreviation {anchorName StringTypeDef}`Str` can be defined:

```anchor StringTypeDef
def Str : Type := String
```

It is then possible to use {anchorName aStr}`Str` as a definition's type instead of {anchorName StringTypeDef}`String`:

```anchor aStr
def aStr : Str := "This is a string."
```

:::

The reason this works is that types follow the same rules as the rest of Lean.
Types are expressions, and in an expression, a defined name can be replaced with its definition.
Because {anchorName aStr}`Str` has been defined to mean {anchorName Book}`String`, the definition of {anchorName aStr}`aStr` makes sense.

## Messages You May Meet
%%%
tag := "abbrev-vs-def"
%%%

:::paragraph
Experimenting with using definitions for types is made more complicated by the way that Lean supports overloaded integer literals.
If {anchorName NaturalNumberTypeDef}`Nat` is too short, a longer name {anchorName NaturalNumberTypeDef}`NaturalNumber` can be defined:

```anchor NaturalNumberTypeDef
def NaturalNumber : Type := Nat
```

However, using {anchorName NaturalNumberTypeDef}`NaturalNumber` as a definition's type instead of {anchorName NaturalNumberTypeDef}`Nat` does not have the expected effect.
In particular, the definition:

```anchor thirtyEight
def thirtyEight : NaturalNumber := 38
```

results in the following error:

```anchorError thirtyEight
failed to synthesize
  OfNat NaturalNumber 38
numerals are polymorphic in Lean, but the numeral `38` cannot be used in a context where the expected type is
  NaturalNumber
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::

This error occurs because Lean allows number literals to be _overloaded_.
When it makes sense to do so, natural number literals can be used for new types, just as if those types were built in to the system.
This is part of Lean's mission of making it convenient to represent mathematics, and different branches of mathematics use number notation for very different purposes.
The specific feature that allows this overloading does not replace all defined names with their definitions before looking for overloading, which is what leads to the error message above.

:::paragraph
One way to work around this limitation is by providing the type {anchorName thirtyEightFixed}`Nat` on the right-hand side of the definition, causing {anchorName thirtyEightFixed}`Nat`'s overloading rules to be used for {anchorTerm thirtyEightFixed}`38`:

```anchor thirtyEightFixed
def thirtyEight : NaturalNumber := (38 : Nat)
```

The definition is still type-correct because {anchorEvalStep NaturalNumberDef 0}`NaturalNumber` is the same type as {anchorEvalStep NaturalNumberDef 1}`Nat`—by definition!
:::

Another solution is to define an overloading for {anchorName NaturalNumberDef}`NaturalNumber` that works equivalently to the one for {anchorName NaturalNumberDef}`Nat`.
This requires more advanced features of Lean, however.

:::paragraph
Finally, defining the new name for {anchorName NaturalNumberDef}`Nat` using {kw}`abbrev` instead of {kw}`def` allows overloading resolution to replace the defined name with its definition.
Definitions written using {kw}`abbrev` are always unfolded.
For instance,

```anchor NTypeDef
abbrev N : Type := Nat
```

and

```anchor thirtyNine
def thirtyNine : N := 39
```

are accepted without issue.
:::

Behind the scenes, some definitions are internally marked as being unfoldable during overload resolution, while others are not.
Definitions that are to be unfolded are called _reducible_.
Control over reducibility is essential to allow Lean to scale: fully unfolding all definitions can result in very large types that are slow for a machine to process and difficult for users to understand.
Definitions produced with {kw}`abbrev` are marked as reducible.
