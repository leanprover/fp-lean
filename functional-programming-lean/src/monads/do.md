# `do`-Notation for Monads

While APIs based on monads are very powerful, the explicit use of `>>=` with anonymous functions is still somewhat noisy.
Just as infix operators are used instead of explicit calls to `HAdd.hAdd`, Lean provides a syntax for monads called _`do`-notation_ that can make programs that use monads easier to read and write.
This is the very same `do`-notation that is used to write programs in `IO`, and `IO` is also a monad.

In [Hello, World!](../hello-world.md), the `do` syntax is used to combine `IO` actions, but the meaning of these programs is explained directly.
Understanding how to program with monads means that `do` can now be explained in terms of how it translates into uses of the underlying monad operators.

The first translation of `do` is used when the only statement in the `do` is a single expression `E`.
In this case, the `do` is removed, so
```lean
{{#example_in Examples/Monads/Do.lean doSugar1}}
```
translates to
```lean
{{#example_out Examples/Monads/Do.lean doSugar1}}
```

The second translation is used when the first statement of the `do` is a `let` with an arrow, binding a local variable.
This translates to a use of `>>=` together with a function that binds that very same variable, so
```lean
{{#example_in Examples/Monads/Do.lean doSugar2}}
```
translates to
```lean
{{#example_out Examples/Monads/Do.lean doSugar2}}
```

When the first statement of the `do` block is an expression, then it is considered to be a monadic action that returns `Unit`, so the function matches the `Unit` constructor and
```lean
{{#example_in Examples/Monads/Do.lean doSugar3}}
```
translates to
```lean
{{#example_out Examples/Monads/Do.lean doSugar3}}
```

Finally, when the first statement of the `do` block is a `let` that uses `:=`, the translated form is an ordinary let expression, so
```lean
{{#example_in Examples/Monads/Do.lean doSugar4}}
```
translates to
```lean
{{#example_out Examples/Monads/Do.lean doSugar4}}
```

The definition of `firstThirdFifthSeventh` that uses the `Monad` class looks like this:
```lean
{{#example_decl Examples/Monads/Class.lean firstThirdFifthSeventhMonad}}
```
Using `do`-notation, it becomes significantly more readable:
```lean
{{#example_decl Examples/Monads/Do.lean firstThirdFifthSeventhDo}}
```

Without the `Monad` type class, the function `number` that numbers the nodes of a tree was written:
```lean
{{#example_decl Examples/Monads.lean numberMonadicish}}
```
With `Monad` and `do`, its definition is much less noisy:
```lean
{{#example_decl Examples/Monads/Do.lean numberDo}}
```


All of the conveniences from `do` with `IO` are also available when using it with other monads.
For example, nested actions also work in any monad.
The original definition of `mapM` was:
```lean
{{#example_decl Examples/Monads/Class.lean mapM}}
```
With `do`-notation, it can be written:
```lean
{{#example_decl Examples/Monads/Do.lean mapM}}
```
Using nested actions makes it almost as short as the original non-monadic `map`:
```lean
{{#example_decl Examples/Monads/Do.lean mapMNested}}
```
Using nested actions, `number` can be made much more concise:
```lean
{{#example_decl Examples/Monads/Do.lean numberDoShort}}
```



## Exercises

 * Rewrite `evaluateM`, its helpers, and the different specific use cases using `do`-notation instead of explicit calls to `>>=`.
 * 
