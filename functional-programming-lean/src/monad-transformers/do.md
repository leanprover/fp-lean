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

Another situation in which early return is useful is command-line applications that terminate early if the arguments or input are incorrect.
Many programs being with a section that validates arguments and inputs before proceeding to the main body of the program.
The following version of [the greeting program `hello-name`](../hello-world/running-a-program.md) checks that no command-line arguments were provided:
```lean
{{#include ../../../examples/early-return/EarlyReturn.lean:main}}
```
Running it with no arguments and typing the name `David` yields the same result as the previous version:
```
$ {{#command {early-return} {early-return} {./run} {lean --run EarlyReturn.lean}}}
{{#command_out {early-return} {./run} }}
```

Providing the name as a command-line argument instead of an answer causes an error:
```
$ {{#command {early-return} {early-return} {./too-many-args} {lean --run EarlyReturn.lean David}}}
{{#command_out {early-return} {./too-many-args} }}
```

And providing no name causes the other error:
```
$ {{#command {early-return} {early-return} {./no-name} {lean --run EarlyReturn.lean}}}
{{#command_out {early-return} {./no-name} }}
```

The program that uses early return avoids needing to nest the control flow, as is done in this version that does not use early return:
```lean
{{#include ../../../examples/early-return/EarlyReturn.lean:nestedmain}}
```


## Loops

Just as every program with mutable state can be rewritten to a program that passes the state as arguments, every loop can be rewritten as a recursive function.
From one perspective, `List.find?` is most clear as a recursive function.
After all, its definition mirrors the structure of the list: if the head passes the check, then it should be returned; otherwise look in the tail.
When no more entries remain, the answer is `none`.
From another perspective, `List.find?` is most clear as a loop.
After all, the program consults the entries in order until a satisfactory one is found, at which point it terminates.
If the loop terminates without having returned, the answer is `none`.

Lean includes a type class that describes looping over a container type in some monad.
This class is called `ForM`:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean ForM}}
```
This class is quite general.
The parameter `m` is a monad with some desired effects, `γ` is the collection to be looped over, and `α` is the type of elements from the collection.
Typically, `m` is allowed to be any monad, but it is possible to have a data structure that e.g. only supports looping in `IO`.
The method `forM` takes a collection, a monadic action to be run for its effects on each element from the collection, and is then responsible for running the actions.

The instance for `List` allows `m` to be any monad, it sets `γ` to be `List α`, and sets the class's `α` to be the same `α` found in the list:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean ListForM}}
```
The instance for `Many` is very similar:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean ManyForM}}
```

Because `γ` can be any type at all, `ForM` can support non-polymorphic collections.
A very simple collection is one of the natural numbers less than some given number, in reverse order:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean AllLessThan}}
```
Its `forM` operator applies the provided action to each smaller `Nat`:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean AllLessThanForM}}
```
Running `IO.println` on each number less than five can be accomplished with `forM`:
```lean
{{#example_in Examples/MonadTransformers/Do.lean AllLessThanForMRun}}
```
```output info
{{#example_out Examples/MonadTransformers/Do.lean AllLessThanForMRun}}
```

* for loops (start by explaining with ForM, then show ForIn)

* An IO-only ForM (maybe bytes from a file handle?)

* ForIn

## Mutable Variables

 * Good demo




## Imperative or Functional Programming?

 * Why not both?
