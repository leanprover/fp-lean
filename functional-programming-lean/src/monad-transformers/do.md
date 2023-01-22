# More do Features

Lean's `do`-notation provides a syntax for writing programs with monads that resembles imperative programming languages.
In addition to providing a convenient syntax for programs with monads, `do`-notation provides syntax for using certain monad transformers.

## Single-Branched `if`

When working in a monad, a common pattern is to carry out a side effect only if some condition is true.
For instance, `countLetters` contains a check for vowels or consonants, and letters that are neither have no effect on the state.
This is captured by having the `else` branch evaluate to `pure ⟨⟩`, which has no effects:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean countLettersModify}}
```

When an `if` is a statement in a `do`-block, rather than being an expression, then `else pure ⟨⟩` can simply be omitted, and Lean inserts it automatically.
The following definition of `countLetters` is completely equivalent:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean countLettersNoElse}}
```
A program that uses a state monad to count the entries in a list that satisfy some monadic check can be written as follows:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean count}}
```

Similarly, `if not E1 then STMT...` can instead be written `unless E1 do STMT...`.
The converse of `count` that counts entries that don't satisfy the monadic check can be written by replacing `if` with `unless`:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean countNot}}
```

Understanding single-branched `if` and `unless` does not require thinking about monad transformers.
They simply replace the missing branch with `pure ⟨⟩`.
The remaining extensions in this section, however, require Lean to automatically rewrite the `do`-block to add a local transformer on top of the requested monad.

## Early Return

The standard library contains a function `List.find?` that returns the first entry in a list that satisfies some check.
A simple implementation that doesn't make use of the fact that `Option` is a monad loops over the list using a recursive function, with an `if` to stop the loop when the desired entry is found:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean findHuhSimple}}
```

Imperative languages typically sport the `return` keyword that aborts the execution of a function, immediately returning some value to the caller.
In Lean, this is available in `do`-notation, and `return` halts the execution of a `do`-block, with `return`'s argument being the value returned from the monad.
In other words, `List.find?` could have been written like this:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean findHuhFancy}}
```

Early return in imperative languages is a bit like an exception that can only cause the current stack frame to be unwound.
Both early return and exceptions terminate execution of a block of code, effectively replacing the surrounding code with the thrown value.
Behind the scenes, early return in Lean is implemented using a version of `ExceptT`.
Each `do`-block that uses early return is wrapped in an exception handler (in the sense of the function `tryCatch`).
Early returns are translated to throwing the value as an exception, and the handlers catch the thrown value and return it immediately.
In other words, the `do`-block's original return value type is also used as the exception type.

Making this more concrete, the helper function `runCatch` strips a layer of `ExceptT` from the top of a monad transformer stack when the exception type and return type are the same:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean runCatch}}
```
The `do`-block in `List.find?` that uses early return is translated to a `do`-block that does not use early return by wrapping it in a use of `runCatch`, and replacing early returns with `throw`:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean desugaredFindHuh}}
```

## Loops

Just as every program with mutable state can be rewritten to a program that passes the state as arguments, every loop can be rewritten as a recursive function.
From one perspective, `List.find?` is most clear as a recursive function.
After all, its definition mirrors the structure of the list: if the head passes the check, then it should be returned; otherwise look in the tail.
When no more entries remain, the answer is `none`.
From another perspective, `List.find?` is most clear as a loop.
After all, the program consults the entries in order until a satisfactory one is found, at which point it terminates.
If the loop terminates without having returned, the answer is `none`.





## Mutable Variables






## Imperative or Functional Programming?

