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

## Leading Dot Notation

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

Using the expected type of an expression to disambiguate a namespace is also applicable to names other than constructors.
If `BinTree.empty` is defined as an alternative way of creating `BinTree`s, then it can also be used with dot notation:
```lean
{{#example_decl Examples/Monads/Conveniences.lean BinTreeEmpty}}

{{#example_in Examples/Monads/Conveniences.lean emptyDot}}
```
```output info
{{#example_out Examples/Monads/Conveniences.lean emptyDot}}
```

## Or-Patterns

In contexts that allow multiple patterns, such as `match`-expressions, multiple patterns may share their result expressions.
The datatype `Weekday` that represents days of the week:
```lean
{{#example_decl Examples/Monads/Conveniences.lean Weekday}}
```

Pattern matching can be used to check whether a day is a weekend:
```lean
{{#example_decl Examples/Monads/Conveniences.lean isWeekendA}}
```
This can already be simplified by using constructor dot notation:
```lean
{{#example_decl Examples/Monads/Conveniences.lean isWeekendB}}
```
Because both weekend patterns have the same result expression (`true`), they can be condensed into one:
```lean
{{#example_decl Examples/Monads/Conveniences.lean isWeekendC}}
```
This can be further simplified into a version in which the argument is not named:
```lean
{{#example_decl Examples/Monads/Conveniences.lean isWeekendD}}
```

Behind the scenes, the result expression is simply duplicated across each pattern.
This means that patterns can bind variables, as in this example that removes the `inl` and `inr` constructors from a sum type in which both contain the same type of value:
```lean
{{#example_decl Examples/Monads/Conveniences.lean condense}}
```
Because the result expression is duplicated, the variables bound by the patterns are not required to have the same types.
Overloaded functions that work for multiple types may be used to write a single result expression that works for patterns that bind variables of different types:
```lean
{{#example_decl Examples/Monads/Conveniences.lean stringy}}
```
In practice, only variables shared in all patterns can be referred to in the result expression, because the result must make sense for each pattern.
In `getTheNat`, only `n` can be accessed, and attempts to use either `x` or `y` lead to errors.
```lean
{{#example_decl Examples/Monads/Conveniences.lean getTheNat}}
```
Attempting to access `x` in a similar definition causes an error because there is no `x` available in the second pattern:
```lean
{{#example_in Examples/Monads/Conveniences.lean getTheAlpha}}
```
```output error
{{#example_out Examples/Monads/Conveniences.lean getTheAlpha}}
```

The fact that the result expression is essentially copy-pasted to each branch of the pattern match can lead to some surprising behavior.
For example, the following definitions are acceptable because the `inr` version of the result expression refers to the global definition of `str`:
```lean
{{#example_decl Examples/Monads/Conveniences.lean getTheString}}
```
Calling this function on both constructors reveals the confusing behavior.
In the first case, a type annotation is needed to tell Lean which type `β` should be:
```lean
{{#example_in Examples/Monads/Conveniences.lean getOne}}
```
```output info
{{#example_out Examples/Monads/Conveniences.lean getOne}}
```
In the second case, the global definition is used:
```lean
{{#example_in Examples/Monads/Conveniences.lean getTwo}}
```
```output info
{{#example_out Examples/Monads/Conveniences.lean getTwo}}
```

Using or-patterns can vastly simplify some definitions and increase their clarity, as in `Weekday.isWeekend`.
Because there is a potential for confusing behavior, it's a good idea to be careful when using them, especially when variables of multiple types or disjoint sets of variables are involved.

