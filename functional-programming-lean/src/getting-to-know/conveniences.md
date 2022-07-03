# Additional Conveniences

Lean contains a number of convenience features that make programs much more concise.

## Automatic Implicit Arguments

When writing polymorphic functions in Lean, it is typically not necessary to list all the implicit arguments.
Instead, they can simply be mentioned.
If Lean can determine their type, then they are automatically inserted as implicit arguments.
In other words, the previous definition of `length`:
```Lean
{{#example_decl Examples/Intro.lean lengthImp}}
```
can be written without `{α : Type}`:
```Lean
{{#example_decl Examples/Intro.lean lengthImpAuto}}
```
This can greatly simplify highly polymorphic definitions that take many implicit arguments.

## Pattern-Matching Definitions

When defining functions with `def`, it is quite common to name an argument and then immediately use it with pattern matching.
For instance, in `length`, the argument `xs` is used only in `match`.
In these situations, the cases of the `match` expression can be written directly, without naming the argument at all.

The first step is to move the arguments' types to the right of the definition's type, in the form of a function type.
For instance, the type of `length` is `List α → Nat`.
Then, replace the `:=` with each case of the pattern match:
```Lean
{{#example_decl Examples/Intro.lean lengthMatchDef}}
```

This syntax can also be used to define functions that take more than one argument.
In this case, their patterns are separated by commas.
For instance, `drop` takes a number _n_ and a list, and returns the list after removing the first _n_ entries.
```Lean
{{#example_decl Examples/Intro.lean drop}}
```

Named arguments and patterns can also be used in the same definition.
For instance, a function that takes a default value and an optional value, and returns the default when the optional value is `none`, can be written:
```Lean
{{#example_decl Examples/Intro.lean fromOption}}
```
This function is called `Option.getD` in the standard library, and can be called with dot notation:
```Lean
{{#example_in Examples/Intro.lean getD}}
```
```Lean info
{{#example_out Examples/Intro.lean getD}}
```
```Lean
{{#example_in Examples/Intro.lean getDNone}}
```
```Lean info
{{#example_out Examples/Intro.lean getDNone}}
```

## Local Definitions

It is often useful to name intermediate steps in a computation.
In many cases, intermediate values represent useful concepts all on their own, and naming them explicitly can make the program easier to read.
In other cases, the intermediate value is used more than once.
As in most other languages, writing down the same code twice in Lean causes it to be computed twice, while saving the result in a variable leads to the result of the computation being saved and re-used.

For instance, `unzip` is a function that transforms a list of pairs into a pair of lists.
When the list of pairs is empty, then the result of `unzip` is a pair of empty lists.
When the list of pairs has a pair at its head, then the two fields of the pair are added to the result of unzipping the rest of the list.
This definition of `unzip` follows that description exactly:
```Lean
{{#example_decl Examples/Intro.lean unzipBad}}
```
Unfortunately, there is a problem: this code is slower than it needs to be.
Each entry in the list of pairs leads to two recursive calls, which makes this function take exponential time.
However, both recursive calls will have the same result, so there is no reason to make the recursive call twice.


In Lean, the result of the recursive call can be named, and thus saved, using `let`.
Local definitions with `let` resemble top-level definitions with `def`: it takes a name to be locally defined, arguments if desired, a type signature, and then a body following `:=`.
After the local definition, the expression in which the local definition is available (called the _body_ of the `let`-expression) must be on a new line, starting at a column in the file that is less than or equal to that of the `let` keyword.
For instance, `let` can be used in `unzip` like this:
```Lean
{{#example_decl Examples/Intro.lean unzip}}
```
To `let` on a single line, separate the local definition from the body with a semicolon.

Local definitions with `let` may also use pattern matching when one pattern is enough to match all cases of a datatype.
In the case of `unzip`, the result of the recursive call is a pair.
Because pairs have only a single constructor, the name `unzipped` can be replaced with a pair pattern:
```Lean
{{#example_decl Examples/Intro.lean unzipPat}}
```
Judicious use of patterns with `let` can make code easier to read, compared to writing the accessor calls by hand.

The biggest difference between `let` and `def` is that recursive `let` definitions must be explicitly indicated by writing `let rec`.
For instance, one way to reverse a list involves a recursive helper function, as in this definition:
```Lean
{{#example_decl Examples/Intro.lean reverse}}
```
The helper function walks down the input list, moving one entry at a time over to `soFar`.
When it reaches the end of the input list, `soFar` contains a reversed version of the input.


## Type Inference

In many situations, Lean can automatically determine an expression's type.
In these cases, explicit types may be omitted from both top-level definitions (with `def`) and local definitions (with `let`).
For instance, the recursive call to `unzip` does not need an annotation:
```Lean
{{#example_decl Examples/Intro.lean unzipNT}}
```

As a rule of thumb, omitting the types of literal values (like strings and numbers) usually works, although Lean may pick a type for literal numbers that is more specific than the intended type.
Lean can usually determine a type for a function application, because it already knows the argument types and the return type.
Omitting return types for function definitions will often work, but function arguments typically require annotations.
Definitions that are not functions, like `unzipped` in the example, do not need types if their bodies do not need types, and the body of this definition is a function application.

Omitting the return type for `unzip` is possible when using an explicit `match` expression:
```Lean
{{#example_decl Examples/Intro.lean unzipNRT}}
```


Generally speaking, it is a good idea to err on the side of too many, rather than too few, type annotations.
First off, explicit types communicate assumptions about the code to readers.
Even if Lean can determine the type on its own, it can still be easier to read code without having to repeatedly query Lean for type information.
Secondly, explicit types help localize errors.
The more explicit a program is about its types, the more informative the error messages can be.
This is especially important in a language like Lean that has a very expressive type system.
Thirdly, explicit types make it easier to write the program in the first place.
The type is a specification, and the compiler's feedback can be a helpful tool in writing a program that meets the specification.
Finally, Lean's type inference is a best-effort system.
Because Lean's type system is so expressive, there is no "best" or most general type to find for all expressions.
This means that even if you get a type, there's no guarantee that it's the _right_ type for a given application.
For instance, `14` can be a `Nat` or an `Int`:
```Lean
{{#example_in Examples/Intro.lean fourteenNat}}
```
```Lean info
{{#example_out Examples/Intro.lean fourteenNat}}
```
```Lean
{{#example_in Examples/Intro.lean fourteenInt}}
```
```Lean info
{{#example_out Examples/Intro.lean fourteenInt}}
```

Missing type annotations can give confusing error messages.
Omitting all types from the definition of `unzip`:
```Lean
{{#example_in Examples/Intro.lean unzipNoTypesAtAll}}
```
leads to a message about the `match` expression:
```Lean error
{{#example_out Examples/Intro.lean unzipNoTypesAtAll}}
```
This is because `match` needs to know the type of the value being inspected, but that type was not available.
A "metavariable" is an unknown part of a program, written `?m.XYZ` in error messages—they are described in the [section on Polymorphism](polymorphism.md).
In this program, the type annotation on the argument is required.

Even some very simple programs require type annotations.
For instance, the identity function just returns whatever argument it is passed.
With argument and type annotations, it looks like this:
```Lean
{{#example_decl Examples/Intro.lean idA}}
```
Lean is capable of determining the return type on its own:
```Lean
{{#example_decl Examples/Intro.lean idB}}
```
Omitting the argument type, however, causes an error:
```Lean
{{#example_in Examples/Intro.lean identNoTypes}}
```
```Lean error
{{#example_out Examples/Intro.lean identNoTypes}}
```

In general, messages that say something like "failed to infer" or that mention metavariables are often a sign that more type annotations are necessary.
Especially while still learning Lean, it is useful to write down many types.

## Simultaneous Matching

Pattern-matching expressions, just like pattern-matching definitions, can match on multiple values at once.
Both the expressions to be inspected and the patterns that they match against are written with commas between them, similarly to the syntax used for definitions.
Here is a version of `drop` that uses simultaneous matching:
```Lean
{{#example_decl Examples/Intro.lean dropMatch}}
```

## Anonymous Functions

Functions in Lean need not be defined at the top level.
As expressions, functions are produced with the `fun` syntax.
Function expressions begin with the keyword `fun`, followed by one or more arguments, which are separated from the return expression using `=>`.
For instance, a function that adds one to a number can be written:
```Lean
{{#example_in Examples/Intro.lean incr}}
```
```Lean info
{{#example_out Examples/Intro.lean incr}}
```
Type annotations are written the same way as on `def`, using parentheses and colons:
```Lean
{{#example_in Examples/Intro.lean incrInt}}
```
```Lean info
{{#example_out Examples/Intro.lean incrInt}}
```
Similarly, implicit arguments may be written with curly braces:
```Lean
{{#example_in Examples/Intro.lean identLambda}}
```
```Lean info
{{#example_out Examples/Intro.lean identLambda}}
```
This style of anonymous function expression is often referred to as a _lambda expression_, because the typical notation used in mathematical descriptions of programming languages uses the Greek letter λ (lambda) where Lean has the keyword `fun`.

Anonymous functions also support the multiple-pattern style used in `def`.
For instance, a function that returns the predecessor of a natural number if it exists can be written:
```Lean
{{#example_in Examples/Intro.lean predHuh}}
```
```Lean info
{{#example_out Examples/Intro.lean predHuh}}
```
Note that Lean's own description of the function has a named argument and a `match` expression.
Many of Lean's convenient syntactic shorthands are expanded to simpler syntax behind the scenes, and the abstraction sometimes leaks.

Definitions using `def` that take arguments may be rewritten as function expressions.
For instance, a function that doubles its argument can be written as follows:
```Lean
{{#example_decl Examples/Intro.lean doubleLambda}}
```

When an anonymous function is very simple, like `{{#example_eval Examples/Intro.lean incrSteps 0}}`, the syntax for creating the function can be fairly verbose.
In that particular example, six non-whitespace characters are used to introduce the function, and its body consists of only three non-whitespace characters.
For these simple cases, Lean provides a shorthand.
In an expression surrounded by parentheses, a centered dot character `·` can stand for an argument, and the expression inside the parentheses becomes the function's body.
That particular function can also be written `{{#example_eval Examples/Intro.lean incrSteps 1}}`.

The centered dot always creates a function out of the _closest_ surrounding set of parentheses.
For instance, `{{#example_eval Examples/Intro.lean funPair 0}}` is a function that returns a pair of numbers, while `{{#example_eval Examples/Intro.lean pairFun 0}}` is a pair of a function and a number.
If multiple dots are used, then they become arguments from left to right.
For instance,
`{{#example_eval Examples/Intro.lean twoDots}}`

Anonymous functions can be applied in precisely the same way as functions defined using `def` or `let`.
The command `{{#example_in Examples/Intro.lean applyLambda}}` results in:
```Lean info
{{#example_out Examples/Intro.lean applyLambda}}
```
while `{{#example_in Examples/Intro.lean applyCdot}}` results in:
```Lean info
{{#example_out Examples/Intro.lean applyCdot}}
```

## Namespaces

Each name in Lean occurs in a _namespace_, which is a collection of names.
Names are placed in namespaces using `.`, so `List.map` is the name `map` in the `List` namespace.
Names in different namespaces do not conflict with each other, even if they are otherwise identical.
This means that `List.map` and `Array.map` are different names.

Names can be directly defined within a namespace.
For instance, the name `double` can be defined in the `Nat` namespace:
```Lean
{{#example_decl Examples/Intro.lean NatDouble}}
```
Because `Nat` is also the name of a type, dot notation is available to call `Nat.double` on expressions with type `Nat`:
```Lean
{{#example_in Examples/Intro.lean NatDoubleFour}}
```
```Lean info
{{#example_out Examples/Intro.lean NatDoubleFour}}
```

In addition to defining names directly in a namespace, a sequence of declarations can be placed in a namespace using the `namespace` and `end` commands.
For instance, this defines `triple` and `quadruple` in the namespace `NewNamespace`:
```Lean
{{#example_decl Examples/Intro.lean NewNamespace}}
```
To refer to them, prefix their names with `NewNamespace.`:
```Lean
{{#example_in Examples/Intro.lean tripleNamespace}}
```
```Lean info
{{#example_out Examples/Intro.lean tripleNamespace}}
```
```Lean
{{#example_in Examples/Intro.lean quadrupleNamespace}}
```
```Lean info
{{#example_out Examples/Intro.lean quadrupleNamespace}}
```

Namespaces may be _opened_, which allows the names in them to be used without explicit qualification.
Writing `open MyNamespace in` before an expression causes the contents of `MyNamespace` to be available in the expression.
For example, `timesTwelve` uses both `quadruple` and `triple` after opening `NewNamespace`:
```Lean
{{#example_decl Examples/Intro.lean quadrupleOpenDef}}
```
Namespaces can also be opened prior to a command.
This allows all parts of the command to refer to the contents of the namespace, rather than just a single expression.
To do this, place the `open ... in` prior to the command.
```Lean
{{#example_in Examples/Intro.lean quadrupleNamespaceOpen}}
```
```Lean info
{{#example_out Examples/Intro.lean quadrupleNamespaceOpen}}
```
Finally, namespaces may be opened for _all_ following commands for the rest of the file.
To do this, simply omit the `in` from a top-level usage of `open`.

## if let

When consuming values that have a sum type, it is often the case that only a single constructor is of interest.
For instance, given this type that represents a subset of Markdown inline elements:
```Lean
{{#example_decl Examples/Intro.lean Inline}}
```
a function that recognizes string elements and extracts their contents can be written:
```Lean
{{#example_decl Examples/Intro.lean inlineStringHuhMatch}}
```
An alternative way of writing this function's body uses `if` together with `let`:
```Lean
{{#example_decl Examples/Intro.lean inlineStringHuh}}
```
This is very much like the pattern-matching `let` syntax.
The difference is that it can be used with sum types, because a fallback is provided in the `else` case.
In some contexts, using `if let` instead of `match` can make code easier to read.

## Positional Structure Arguments

The [section on structures](structures.md) presents two ways of constructing structures:
 1. The constructor can be called directly, as in `{{#example_in Examples/Intro.lean pointCtor}}`.
 2. Brace notation can be used, as in `{{#example_in Examples/Intro.lean pointBraces}}`.

In some contexts, it can be convenient to pass arguments positionally, rather than by name, but without naming the constructor directly.
For instance, defining a variety of similar structure types can help keep domain concepts separate, but the natural way to read the code may treat each of them as being essentially a tuple.
In these contexts, the arguments can be enclosed in angle brackets `⟨` and `⟩`.
A `Point` can be written `{{#example_in Examples/Intro.lean pointPos}}`.
Be careful!
Even though they look like the less-than sign `<` and greater-than sign `>`, these brackets are different.

Just as with the brace notation for named constructor arguments, this positional syntax can only be used in a context where Lean can determine the structure's type, either from a type annotation or from other type information in the program.
For instance, `{{#example_in Examples/Intro.lean pointPosEvalNoType}}` yields the following error:
```Lean error
{{#example_out Examples/Intro.lean pointPosEvalNoType}}
```
The metavariable in the error is because there is no type information available.
Adding an annotation, such as in `{{#example_in Examples/Intro.lean pointPosEvalNoType}}`, solves the problem:
```Lean info
{{#example_out Examples/Intro.lean pointPosEvalNoType}}
```


## String Interpolation

In Lean, prefixing a string with `s!` triggers _interpolation_, where expressions contained in curly braces inside the string are replaced with their values.
This is similar to `f`-strings in Python and `$`-prefixed strings in C#.
For instance,
```Lean
{{#example_in Examples/Intro.lean interpolation}}
```
yields the output
```Lean info
{{#example_out Examples/Intro.lean interpolation}}
```

Not all expressions can be interpolated into a string.
For instance, attempting to interpolate a function results in an error.
```Lean
{{#example_in Examples/Intro.lean interpolationOops}}
```
yields the output
```Lean info
{{#example_out Examples/Intro.lean interpolationOops}}
```
This is because there is no standard way to convert functions into strings.
The Lean compiler maintains a table that describes how to convert values of various types into strings, and the message `failed to synthesize instance` means that the Lean compiler didn't find an entry in this table for the given type.
This uses the same language feature as the `deriving Repr` syntax that was described in the [section on structures](structures.md).
