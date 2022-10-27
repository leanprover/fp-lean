# Monads

In C# and Kotlin, the `?.` operator is a way to look up a property or call a method on a potentially-null value.
If the reciever is `null`, the whole expression is null.
Otherwise, the underlying non-`null` value receives the call.
Uses of `?.` can be chained, in which case the first `null` result terminates the chain of lookups.

In Lean, pattern matching can be used to chain checks for null.
Getting the first entry from a list can just use the optional indexing notation:
```lean
{{#example_decl Examples/Monads.lean first}}
```
The result must be an `Option` because empty lists have no first entry.
Extracting the first and third entries requires a check that each is not `none`:
```lean
{{#example_decl Examples/Monads.lean firstThird}}
```
Similarly, extracting the first, third, and fifth entries requires more checks that the values are not `none`:
```lean
{{#example_decl Examples/Monads.lean firstThirdFifth}}
```
And adding the seventh entry to this sequence begins to become quite unmanageable:
```lean
{{#example_decl Examples/Monads.lean firstThirdFifthSeventh}}
```

## Checking for `none`: Don't Repeat Yourself

The fundamental problem with this code is that it addresses two concerns: extracting the numbers and checking that all of them are present, but the second concern is addressed by copying and pasting the code that handles the `none` case.
It is often good style to lift a repetitive segment into a helper function:
```lean
{{#example_decl Examples/Monads.lean andThenOption}}
```
This helper, which is used similarly to `?.` in C# and Kotlin, takes care of propagating `none` values.
It takes two arguments: an optional value and a function to apply when the value is not `none`.
If the first argument is `none`, then the helper returns `none`.
If the first argument is not `none`, then the function is applied to the contents of the `some` constructor.

Now, `firstThird` can be rewritten to use `andThen` instead of pattern matching:
```lean
{{#example_decl Examples/Monads.lean firstThirdandThen}}
```
In Lean, functions don't need to be enclosed in parentheses when passed as arguments.
The following equivalent definition uses more parentheses and indents the bodies of functions:
```lean
{{#example_decl Examples/Monads.lean firstThirdandThenExpl}}
```
The `andThen` helper provides a sort of "pipeline" through which values flow, and the version with the somewhat unusual indentation is more suggestive of this fact.
Improving the syntax used to write `andThen` can make these computations even easier to understand.

### Infix Operators

In Lean, infix operators can be declared using the `infix`, `infixl`, and `infixr` commands, which create (respectively) non-associative, left-associative, and right-associative operators.
When used multiple times in a row, a _left associative_ operator stacks up the opening parentheses on the left side of the expression.
The addition operator `+` is left associative, so `{{#example_in Examples/Monads.lean plusFixity}}` is equivalent to `{{#example_out Examples/Monads.lean plusFixity}}`.
The exponentiation operator `^` is right associative, so `{{#example_in Examples/Monads.lean powFixity}}` is equivalent to `{{#example_out Examples/Monads.lean powFixity}}`.
Comparison operators such as `<` are non-associative, so `x < y < z` is a syntax error and requires manual parentheses.

The following declaration makes `andThen` into an infix operator:
```lean
{{#example_decl Examples/Monads.lean andThenOptArr}}
```
The number following the colon declares the _precedence_ of the new infix operator.
In ordinary mathematical notation, `{{#example_in Examples/Monads.lean plusTimesPrec}}` is equivalent to `{{#example_out Examples/Monads.lean plusTimesPrec}}` even though both `+` and `*` are left associative.
In Lean, `+` has precedence 65 and `*` has precedence 70.
Higher-precedence operators are applied before lower-precedence operators.
According to the declaration of `~~>`, both `+` and `*` have higher precedence, and thus apply first.
Typically, figuring out the most convenient precedences for a group of operators requires some experimentation and a large collection of examples.

Following the new infix operator is a double arrow `=>`, which specifies the named function to be used for the infix operator.
Lean's standard library uses this feature to define `+` and `*` as infix operators that point at `HAdd.hAdd` and `HMul.hMul`, respectively, allowing type classes to be used for overloading.
Here, however, `andThen` is just an ordinary function.

Having defined an infix operator for `andThen`, `firstThird` can be rewritten in a way that brings the "pipeline" feeling of `none`-checks front and center:
```lean
{{#example_decl Examples/Monads.lean firstThirdInfix}}
```
This style is much more concise when writing larger functions:
```lean
{{#example_decl Examples/Monads.lean firstThirdFifthSeventInfix}}
```

## Propagating Error Messages

