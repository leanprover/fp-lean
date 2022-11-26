# Additional Conveniences

## Shared Argument Types

When defining a function that takes multiple arguments that have the same type, both can be written before the same colon.
For example,
```lean
{{#example_decl Examples/Monads/Conveniences.lean equalHuhOld}}
```
can be written
```lean
{{#example_decl Examples/Monads/Conveniences.lean equalHuhNew}}
```
This is especially useful when the type signature is large.

## Constructor Dot Notation

The constructors of an inductive type are in a namespace.
This allows multiple related inductive types to use the same constructor names, but it can lead to programs becoming verbose.
In contexts where the inductive type in question is known, the namespace can be omitted by preceding the constructor's name with a dot, and Lean uses the expected type to resolve the constructor names.
For example, a function that mirrors a binary tree can be written:
```lean
{{#example_decl Examples/Monads/Conveniences.lean mirrorOld}}
```
Omitting the namespaces makes it significantly shorter, at the cost of making the program harder to read in contexts like code review tools that don't include the Lean compiler:
```lean
{{#example_decl Examples/Monads/Conveniences.lean mirrorNew}}
```



