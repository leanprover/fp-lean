import VersoManual
import FPLean.Examples

open Verso.Genre Manual

open FPLean

example_module Examples.Intro

#doc (Manual) "Additional Conveniences" =>

Lean contains a number of convenience features that make programs much more concise.

# Automatic Implicit Parameters

:::paragraph
When writing polymorphic functions in Lean, it is typically not necessary to list all the implicit parameters.
Instead, they can simply be mentioned.
If Lean can determine their type, then they are automatically inserted as implicit parameters.
In other words, the previous definition of {term}`lengthImp.name`:

{exampleDecl lengthImp}

can be written without `{α : Type}`:

{exampleDecl lengthImpAuto}

This can greatly simplify highly polymorphic definitions that take many implicit parameters.

:::

# Pattern-Matching Definitions

When defining functions with {kw}`def`, it is quite common to name an argument and then immediately use it with pattern matching.
For instance, in {term}`lengthImp.name`, the argument {term}`lengthImp.xs` is used only in {kw}`match`.
In these situations, the cases of the {kw}`match` expression can be written directly, without naming the argument at all.

:::paragraph
The first step is to move the arguments' types to the right of the colon, so the return type is a function type.
For instance, the type of {term}`lengthMatchDef.name` is {term}`lengthMatchDef.rtype`.
Then, replace the `:=` with each case of the pattern match:

{exampleDecl lengthMatchDef}

This syntax can also be used to define functions that take more than one argument.
In this case, their patterns are separated by commas.
For instance, {term}`drop.name` takes a number $`n` and a list, and returns the list after removing the first $`n` entries.

{exampleDecl drop}

:::

:::paragraph

Named arguments and patterns can also be used in the same definition.
For instance, a function that takes a default value and an optional value, and returns the default when the optional value is {term}`none.name`, can be written:

{exampleDecl fromOption}

This function is called {term}`Option.getD.name` in the standard library, and can be called with dot notation:

{exampleIn getD}


{exampleInfo getD}


{exampleIn getDNone}


{exampleInfo getDNone}

:::

# Local Definitions

It is often useful to name intermediate steps in a computation.
In many cases, intermediate values represent useful concepts all on their own, and naming them explicitly can make the program easier to read.
In other cases, the intermediate value is used more than once.
As in most other languages, writing down the same code twice in Lean causes it to be computed twice, while saving the result in a variable leads to the result of the computation being saved and re-used.

:::paragraph

For instance, {term}`unzipBad.name` is a function that transforms a list of pairs into a pair of lists.
When the list of pairs is empty, then the result of {term}`unzipBad.name` is a pair of empty lists.
When the list of pairs has a pair at its head, then the two fields of the pair are added to the result of unzipping the rest of the list.
This definition of {term}`unzipBad.name` follows that description exactly:

{exampleDecl unzipBad}

Unfortunately, there is a problem: this code is slower than it needs to be.
Each entry in the list of pairs leads to two recursive calls, which makes this function take exponential time.
However, both recursive calls will have the same result, so there is no reason to make the recursive call twice.

:::

:::paragraph

In Lean, the result of the recursive call can be named, and thus saved, using {kw}`let`.
Local definitions with {kw}`let` resemble top-level definitions with {kw}`def`: it takes a name to be locally defined, arguments if desired, a type signature, and then a body following `:=`.
After the local definition, the expression in which the local definition is available (called the _body_ of the {kw}`let`-expression) must be on a new line, starting at a column in the file that is less than or equal to that of the {kw}`let` keyword.
A local definition with {kw}`let` in {term}`unzip.name` looks like this:

{exampleDecl unzip}

To use {kw}`let` on a single line, separate the local definition from the body with a semicolon.
:::

:::paragraph
Local definitions with {kw}`let` may also use pattern matching when one pattern is enough to match all cases of a datatype.
In the case of {term}`unzip.name`, the result of the recursive call is a pair.
Because pairs have only a single constructor, the name `unzipped` can be replaced with a pair pattern:

{exampleDecl unzipPat}

Judicious use of patterns with {kw}`let` can make code easier to read, compared to writing the accessor calls by hand.
:::

:::paragraph
The biggest difference between {kw}`let` and {kw}`def` is that recursive {kw}`let` definitions must be explicitly indicated by writing {kw}`let rec`.
For instance, one way to reverse a list involves a recursive helper function, as in this definition:

{exampleDecl reverse}

The helper function walks down the input list, moving one entry at a time over to {term}`reverse.soFar`.
When it reaches the end of the input list, {term}`reverse.soFar` contains a reversed version of the input.
:::

# Type Inference

:::paragraph
In many situations, Lean can automatically determine an expression's type.
In these cases, explicit types may be omitted from both top-level definitions (with {kw}`def`) and local definitions (with {kw}`let`).
For example, the recursive call to {term}`unzipNT.name` does not need an annotation:

{exampleDecl unzipNT}

:::

As a rule of thumb, omitting the types of literal values (like strings and numbers) usually works, although Lean may pick a type for literal numbers that is more specific than the intended type.
Lean can usually determine a type for a function application, because it already knows the argument types and the return type.
Omitting return types for function definitions will often work, but function parameters typically require annotations.
Definitions that are not functions, like {term}`unzipNT.unzipped` in the example, do not need type annotations if their bodies do not need type annotations, and the body of this definition is a function application.

:::paragraph
Omitting the return type for {term}`unzipNRT.name` is possible when using an explicit {kw}`match` expression:

{exampleDecl unzipNRT}

:::

:::paragraph

Generally speaking, it is a good idea to err on the side of too many, rather than too few, type annotations.
First off, explicit types communicate assumptions about the code to readers.
Even if Lean can determine the type on its own, it can still be easier to read code without having to repeatedly query Lean for type information.
Secondly, explicit types help localize errors.
The more explicit a program is about its types, the more informative the error messages can be.
This is especially important in a language like Lean that has a very expressive type system.
Thirdly, explicit types make it easier to write the program in the first place.
The type is a specification, and the compiler's feedback can be a helpful tool in writing a program that meets the specification.
Finally, Lean's type inference is a best-effort system.
Because Lean's type system is so expressive, there is no “best” or most general type to find for all expressions.
This means that even if you get a type, there's no guarantee that it's the _right_ type for a given application.
For instance, `14` can be a {term}`Nat.name` or an {term}`Int.name`:

{exampleIn fourteenNat}


{exampleInfo fourteenNat}


{exampleIn fourteenInt}


{exampleInfo fourteenInt}

:::

:::paragraph
Missing type annotations can give confusing error messages.
Omitting all types from the definition of {term}`unzipNoTypesAtAll.name`:

{exampleIn unzipNoTypesAtAll}

leads to a message about the {kw}`match` expression:

{exampleError unzipNoTypesAtAll}

This is because {kw}`match` needs to know the type of the value being inspected, but that type was not available.
A “metavariable” is an unknown part of a program, written `?m.XYZ` in error messages—they are described in the [section on Polymorphism](polymorphism.md).
In this program, the type annotation on the argument is required.
:::

:::paragraph
Even some very simple programs require type annotations.
For instance, the identity function just returns whatever argument it is passed.
With argument and type annotations, it looks like this:

{exampleDecl idA}

Lean is capable of determining the return type on its own:

{exampleDecl idB}

Omitting the argument type, however, causes an error:

{exampleIn identNoTypes}


```exampleError identNoTypes
failed to infer binder type
```
:::

In general, messages that say something like “failed to infer” or that mention metavariables are often a sign that more type annotations are necessary.
Especially while still learning Lean, it is useful to provide most types explicitly.

# Simultaneous Matching

:::paragraph

Pattern-matching expressions, just like pattern-matching definitions, can match on multiple values at once.
Both the expressions to be inspected and the patterns that they match against are written with commas between them, similarly to the syntax used for definitions.
Here is a version of {term}`dropMatch.name` that uses simultaneous matching:

{exampleDecl dropMatch}

:::

:::paragraph

Simultaneous matching resembles matching on a pair, but there is an important difference.
Lean tracks the connection between the expression being matched and the patterns, and this information is used for purposes that include checking for termination and propagating static type information.
As a result, the version of {term}`sameLengthPair.name` that matches a pair is rejected by the termination checker, because the connection between {term}`sameLengthPair.xs` and {term}`sameLengthPair.x_xs` is obscured by the intervening pair:

{exampleIn sameLengthPair}

{exampleError sameLengthPair}

Simultaneously matching both lists is accepted:

{exampleDecl sameLengthOk2}

:::

# Natural Number Patterns

:::paragraph

In the section on [datatypes and patterns](datatypes-and-patterns.md), {term}`even.name` was defined like this:

{exampleDecl even}

Just as there is special syntax to make list patterns more readable than using {term}`List.cons.name` and {term}`List.nil.name` directly, natural numbers can be matched using literal numbers and `+`.
For example, {term}`evenFancy.name` can also be defined like this:

{exampleDecl evenFancy}


In this notation, the arguments to the `+` pattern serve different roles.
Behind the scenes, the left argument ({term}`evenFancy.n` above) becomes an argument to some number of {term}`Nat.succ.name` patterns, and the right argument ({term}`evenFancy.one` above) determines how many {term}`Nat.succ.name`s to wrap around the pattern.
The explicit patterns in {term}`explicitHalve.name`, which divides a {term}`Nat.name` by two and drops the remainder:

{exampleDecl explicitHalve}

can be replaced by numeric literals and `+`:

{exampleDecl halve}

Behind the scenes, both definitions are completely equivalent.
Remember: {term}`halve.recur` is equivalent to {term}`halveParens.one`, not {term}`halveParens.two`.

:::

:::paragraph

When using this syntax, the second argument to `+` should always be a literal {term}`Nat.name`.
Even though addition is commutative, flipping the arguments in a pattern can result in errors like the following:

{exampleIn halveFlippedPat}

{exampleError halveFlippedPat}

This restriction enables Lean to transform all uses of the `+` notation in a pattern into uses of the underlying {term}`Nat.succ.name`, keeping the language simpler behind the scenes.

:::

# Anonymous Functions

:::paragraph

Functions in Lean need not be defined at the top level.
As expressions, functions are produced with the {kw}`fun` syntax.
Function expressions begin with the keyword {kw}`fun`, followed by one or more parameters, which are separated from the return expression using `=>`.
For instance, a function that adds one to a number can be written:

{exampleIn incr}

{exampleInfo incr}

Type annotations are written the same way as on {kw}`def`, using parentheses and colons:

{exampleIn incrInt}


{exampleInfo incrInt}

Similarly, implicit parameters may be written with curly braces:

{exampleIn identLambda}

{exampleInfo identLambda}

This style of anonymous function expression is often referred to as a _lambda expression_, because the typical notation used in mathematical descriptions of programming languages uses the Greek letter λ (lambda) where Lean has the keyword {kw}`fun`.
Even though Lean does permit {kw}`λ` to be used instead of {kw}`fun`, it is most common to write {kw}`fun`.

:::

:::paragraph

Anonymous functions also support the multiple-pattern style used in {kw}`def`.
For instance, a function that returns the predecessor of a natural number if it exists can be written:

{exampleIn predHuh}


{exampleInfo predHuh}

Note that Lean's own description of the function has a named argument and a {kw}`match` expression.
Many of Lean's convenient syntactic shorthands are expanded to simpler syntax behind the scenes, and the abstraction sometimes leaks.

:::

:::paragraph

Definitions using {kw}`def` that take arguments may be rewritten as function expressions.
For instance, a function that doubles its argument can be written as follows:

{exampleDecl doubleLambda}


When an anonymous function is very simple, like {exampleEval 0}`incrSteps`, the syntax for creating the function can be fairly verbose.
In that particular example, six non-whitespace characters are used to introduce the function, and its body consists of only three non-whitespace characters.
For these simple cases, Lean provides a shorthand.
In an expression surrounded by parentheses, a centered dot character `·` can stand for an parameter, and the expression inside the parentheses becomes the function's body.
That particular function can also be written {exampleEval 1}`incrSteps`.
:::

:::paragraph

The centered dot always creates a function out of the _closest_ surrounding set of parentheses.
For instance, {exampleEval 0}`funPair` is a function that returns a pair of numbers, while {exampleEval 0}`pairFun` is a pair of a function and a number.
If multiple dots are used, then they become parameters from left to right:

{exampleEval twoDots}

Anonymous functions can be applied in precisely the same way as functions defined using {kw}`def` or {kw}`let`.
The command {exampleIn}`applyLambda` results in:

{exampleInfo applyLambda}

while {exampleIn}`applyCdot` results in:

{exampleInfo applyCdot}

:::

# Namespaces


Each name in Lean occurs in a _namespace_, which is a collection of names.
Names are placed in namespaces using `.`, so `List.map` is the name `map` in the `List` namespace.
Names in different namespaces do not conflict with each other, even if they are otherwise identical.
This means that {term}`List.map.name` and {term}`Array.map.name` are different names.
Namespaces may be nested, so `Project.Frontend.User.loginTime` is the name `loginTime` in the nested namespace `Project.Frontend.User`.

:::paragraph
Names can be directly defined within a namespace.
For instance, the name {term}`double.name` can be defined in the {term}`Nat.name` namespace:

{exampleDecl NatDouble}

Because {term}`Nat.name` is also the name of a type, dot notation is available to call {term}`Nat.double.name` on expressions with type {term}`Nat.name`:

{exampleIn NatDoubleFour}

{exampleInfo NatDoubleFour}

:::

:::paragraph

In addition to defining names directly in a namespace, a sequence of declarations can be placed in a namespace using the {kw}`namespace` and {kw}`end` commands.
For instance, this defines {term}`triple` and {term}`quadruple` in the namespace `NewNamespace`:

{exampleDecl NewNamespace}

To refer to them, prefix their names with `NewNamespace.`:

{exampleIn tripleNamespace}

{exampleInfo tripleNamespace}


{exampleIn quadrupleNamespace}

{exampleInfo quadrupleNamespace}

:::

:::paragraph
Namespaces may be _opened_, which allows the names in them to be used without explicit qualification.
Writing `open MyNamespace in` before an expression causes the contents of `MyNamespace` to be available in the expression.
For example, {term}`timesTwelve` uses both {term}`quadruple` and {term}`triple` after opening `NewNamespace`:

{exampleDecl quadrupleOpenDef}

:::

:::paragraph
Namespaces can also be opened prior to a command.
This allows all parts of the command to refer to the contents of the namespace, rather than just a single expression.
To do this, place the {kw}`open`﻿` ... `{kw}`in` prior to the command.

{exampleIn quadrupleNamespaceOpen}

{exampleInfo quadrupleNamespaceOpen}

Function signatures show the name's full namespace.
Namespaces may additionally be opened for _all_ following commands for the rest of the file.
To do this, simply omit the {kw}`in` from a top-level usage of {kw}`open`.

:::

# if let

:::paragraph
When consuming values that have a sum type, it is often the case that only a single constructor is of interest.
For example, given this type that represents a subset of Markdown inline elements:

{exampleDecl Inline}

a function that recognizes string elements and extracts their contents can be written:

{exampleDecl inlineStringHuhMatch}

:::

:::paragraph
An alternative way of writing this function's body uses {kw}`if` together with {kw}`let`:

{exampleDecl inlineStringHuh}

This is very much like the pattern-matching {kw}`let` syntax.
The difference is that it can be used with sum types, because a fallback is provided in the {kw}`else` case.
In some contexts, using {kw}`if let` instead of {kw}`match` can make code easier to read.

:::

# Positional Structure Arguments

The [section on structures](structures.md) presents two ways of constructing structures:
 1. The constructor can be called directly, as in {exampleIn}`pointCtor`.
 2. Brace notation can be used, as in {exampleIn}`pointBraces`.

In some contexts, it can be convenient to pass arguments positionally, rather than by name, but without naming the constructor directly.
For instance, defining a variety of similar structure types can help keep domain concepts separate, but the natural way to read the code may treat each of them as being essentially a tuple.
In these contexts, the arguments can be enclosed in angle brackets `⟨` and `⟩`.
A {term}`Point.name` can be written {exampleIn}`pointPos`.
Be careful!
Even though they look like the less-than sign `<` and greater-than sign `>`, these brackets are different.
They can be input using `\<` and `\>`, respectively.

:::paragraph
Just as with the brace notation for named constructor arguments, this positional syntax can only be used in a context where Lean can determine the structure's type, either from a type annotation or from other type information in the program.
For instance, {exampleIn}`pointPosEvalNoType` yields the following error:

{exampleError pointPosEvalNoType}

The metavariable in the error is because there is no type information available.
Adding an annotation, such as in {exampleIn}`pointPosWithType`, solves the problem:

{exampleInfo pointPosWithType}

:::

# String Interpolation

:::paragraph
In Lean, prefixing a string with {kw}`s!` triggers _interpolation_, where expressions contained in curly braces inside the string are replaced with their values.
This is similar to `f`-strings in Python and `$`-prefixed strings in C#.
For instance,

{exampleIn interpolation}

yields the output

{exampleInfo interpolation}

:::

:::paragraph
Not all expressions can be interpolated into a string.
For instance, attempting to interpolate a function results in an error.

{exampleIn interpolationOops}

yields the error

{exampleError interpolationOops}

This is because there is no standard way to convert functions into strings.
The Lean compiler maintains a table that describes how to convert values of various types into strings, and the message `failed to synthesize instance` means that the Lean compiler didn't find an entry in this table for the given type.
This uses the same language feature as the `deriving Repr` syntax that was described in the [section on structures](structures.md).
:::
