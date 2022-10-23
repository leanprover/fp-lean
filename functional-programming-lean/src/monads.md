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

The fundamental problem with this code is that it addresses two concerns: extracting the numbers and checking that all of them are present, but the second concern is addressed by copying and pasting the code that handles the `none` case.
It is often good style to lift a repetitive segment into a helper function:
```lean
{{#example_decl Examples/Monads.lean andThenOption}}
```
This helper, which is used similarly to `?.` in C# and Kotlin, takes care of propagating `none`-ness.
It takes two arguments: an optional value and a function to apply when the value is not `none`.
If the first argument is `none`, then the helper returns `none`.
If the first argument is not `none`, then the function is applied to the contents of the `some` constructor.

Now, `firstThird` can be rewritten to use `andThen` instead of pattern matching:
```lean
{{#example_decl Examples/Monads.lean firstThirdandThen}}
```
