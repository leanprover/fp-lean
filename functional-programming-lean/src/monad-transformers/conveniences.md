# Additional Conveniences

## Pipe Operators

Functions are normally written before their arguments.
When reading a program from left to right, this promotes a view in which the function's _output_ is paramount—the function has a goal to achieve (that is, a value to compute), and it receives arguments to support it in this process.
But some programs are easier to understand in terms of an input that is successively refined to produce the output.
For these situations, Lean provides a _pipeline_ operator which is similar to the that provided by F#.
Pipeline operators are useful in the same situations as Clojure's threading macros.

The pipeline `{{#example_in Examples/MonadTransformers/Conveniences.lean pipelineShort}}` is short for `{{#example_out Examples/MonadTransformers/Conveniences.lean pipelineShort}}`.
For example, evaluating:
```lean
{{#example_in Examples/MonadTransformers/Conveniences.lean some5}}
```
results in:
```output info
{{#example_out Examples/MonadTransformers/Conveniences.lean some5}}
```
While this change of emphasis can make some programs more convenient to read, pipelines really come into their own when they contain many components.

With the definition:
```lean
{{#example_decl Examples/MonadTransformers/Conveniences.lean times3}}
```
the following pipeline:
```lean
{{#example_in Examples/MonadTransformers/Conveniences.lean itIsFive}}
```
yields:
```output info
{{#example_out Examples/MonadTransformers/Conveniences.lean itIsFive}}
```
More generally, a series of pipelines `{{#example_in Examples/MonadTransformers/Conveniences.lean pipeline}}` is short for nested function applications `{{#example_out Examples/MonadTransformers/Conveniences.lean pipeline}}`.

Pipelines may also be written in reverse.
In this case, they do not place the subject of data transformation first; however, in cases where many nested parentheses pose a challenge for readers, they can clarify the steps of application.
The prior example could be equivalently written as:
```lean
{{#example_in Examples/MonadTransformers/Conveniences.lean itIsAlsoFive}}
```
which is short for:
```lean
{{#example_in Examples/MonadTransformers/Conveniences.lean itIsAlsoFiveParens}}
```

Lean's method dot notation that uses the name of the type before the dot to resolve the namespace of the operator after the dot serves a similar purpose to pipelines.
Even without the pipeline operator, it is possible to write `{{#example_in Examples/MonadTransformers/Conveniences.lean listReverse}}` instead of `{{#example_out Examples/MonadTransformers/Conveniences.lean listReverse}}`.
However, the pipeline operator is also useful for dotted functions when using many of them.
`{{#example_in Examples/MonadTransformers/Conveniences.lean listReverseDropReverse}}` can also be written as `{{#example_out Examples/MonadTransformers/Conveniences.lean listReverseDropReverse}}`.
This version avoids having to parenthesize expressions simply because they accept arguments, and it recovers the convenience of a chain of method calls in languages like Kotlin or C#.
However, it still requires the namespace to be provided by hand.
As a final convenience, Lean provides the "pipeline dot" operator, which groups functions like the pipeline but uses the name of the type to resolve namespaces.
With "pipeline dot", the example can be rewritten to `{{#example_out Examples/MonadTransformers/Conveniences.lean listReverseDropReversePipe}}`.

## Infinite Loops

Within a `do`-block, the `repeat` keyword introduces an infinite loop.
For example, a program that spams the string `"Spam!"` can use it:
```lean
{{#example_decl Examples/MonadTransformers/Conveniences.lean spam}}
```
A `repeat` loop supports `break` and `continue`, just like `for` loops.

The `dump` function from the [implementation of `feline`](../hello-world/cat.md#streams) uses a recursive function to run forever:
```lean
{{#include ../../../examples/feline/2/Main.lean:dump}}
```
This function can be greatly shortened using `repeat`:
```lean
{{#example_decl Examples/MonadTransformers/Conveniences.lean dump}}
```

Neither `spam` nor `dump` need to be declared as `partial` because they are not themselves infinitely recursive.
Instead, `repeat` makes use of a type whose `ForM` instance is `partial`.
Partiality does not "infect" calling functions.

## While Loops

When programming with local mutability, `while` loops can be a convenient alternative to `repeat` with an `if`-guarded `break`:
```lean
{{#example_decl Examples/MonadTransformers/Conveniences.lean dumpWhile}}
```
Behind the scenes, `while` is just a simpler notation for `repeat`.

