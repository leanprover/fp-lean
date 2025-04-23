# More do Features

Lean's `do`-notation provides a syntax for writing programs with monads that resembles imperative programming languages.
In addition to providing a convenient syntax for programs with monads, `do`-notation provides syntax for using certain monad transformers.

## Single-Branched `if`

When working in a monad, a common pattern is to carry out a side effect only if some condition is true.
For instance, `countLetters` contains a check for vowels or consonants, and letters that are neither have no effect on the state.
This is captured by having the `else` branch evaluate to `pure ()`, which has no effects:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean countLettersModify}}
```

When an `if` is a statement in a `do`-block, rather than being an expression, then `else pure ()` can simply be omitted, and Lean inserts it automatically.
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
They simply replace the missing branch with `pure ()`.
The remaining extensions in this section, however, require Lean to automatically rewrite the `do`-block to add a local transformer on top of the monad that the `do`-block is written in.

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
Many programs begin with a section that validates arguments and inputs before proceeding to the main body of the program.
The following version of [the greeting program `hello-name`](../hello-world/running-a-program.md) checks that no command-line arguments were provided:
```lean
{{#include ../../../examples/early-return/EarlyReturn.lean:main}}
```
Running it with no arguments and typing the name `David` yields the same result as the previous version:
```
$ {{#command {early-return} {early-return} {./run} {lean --run EarlyReturn.lean}}}
{{#command_out {early-return} {./run} {early-return/expected}}}
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

One important difference between early return in Lean and early return in imperative languages is that Lean's early return applies only to the current `do`-block.
When the entire definition of a function is in the same `do` block, this difference doesn't matter.
But if `do` occurs underneath some other structures, then the difference becomes apparent.
For example, given the following definition of `greet`:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean greet}}
```
the expression `{{#example_in Examples/MonadTransformers/Do.lean greetDavid}}` evaluates to `{{#example_out Examples/MonadTransformers/Do.lean greetDavid}}`, not just `"David"`.

## Loops

Just as every program with mutable state can be rewritten to a program that passes the state as arguments, every loop can be rewritten as a recursive function.
From one perspective, `List.find?` is most clear as a recursive function.
After all, its definition mirrors the structure of the list: if the head passes the check, then it should be returned; otherwise look in the tail.
When no more entries remain, the answer is `none`.
From another perspective, `List.find?` is most clear as a loop.
After all, the program consults the entries in order until a satisfactory one is found, at which point it terminates.
If the loop terminates without having returned, the answer is `none`.

### Looping with ForM

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
The [function `doList` from `doug`](reader-io.md#implementation) is `forM` for lists.
Because `forM` is intended to be used in `do`-blocks, it uses `Monad` rather than `Applicative`.
`forM` can be used to make `countLetters` much shorter:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean countLettersForM}}
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

An example `ForM` instance that works only in a particular monad is one that loops over the lines read from an IO stream, such as standard input:
```lean
{{#include ../../../examples/formio/ForMIO.lean:LinesOf}}
```
The definition of `forM` is marked `partial` because there is no guarantee that the stream is finite.
In this case, `IO.FS.Stream.getLine` works only in the `IO` monad, so no other monad can be used for looping.

This example program uses this looping construct to filter out lines that don't contain letters:
```lean
{{#include ../../../examples/formio/ForMIO.lean:main}}
```
The file `test-data` contains:
```
{{#include ../../../examples/formio/test-data}}
```
Invoking this program, which is stored in `ForMIO.lean`, yields the following output:
```
$ {{#command {formio} {formio} {lean --run ForMIO.lean < test-data}}}
{{#command_out {formio} {lean --run ForMIO.lean < test-data} {formio/expected}}}
```

### Stopping Iteration

Terminating a loop early is difficult to do with `forM`.
Writing a function that iterates over the `Nat`s in an `AllLessThan` only until `3` is reached requires a means of stopping the loop partway through.
One way to achieve this is to use `forM` with the `OptionT` monad transformer.
The first step is to define `OptionT.exec`, which discards information about both the return value and whether or not the transformed computation succeeded:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean OptionTExec}}
```
Then, failure in the `OptionT` instance of `Alternative` can be used to terminate looping early:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean OptionTcountToThree}}
```
A quick test demonstrates that this solution works:
```lean
{{#example_in Examples/MonadTransformers/Do.lean optionTCountSeven}}
```
```output info
{{#example_out Examples/MonadTransformers/Do.lean optionTCountSeven}}
```

However, this code is not so easy to read.
Terminating a loop early is a common task, and Lean provides more syntactic sugar to make this easier.
This same function can also be written as follows:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean countToThree}}
```
Testing it reveals that it works just like the prior version:
```lean
{{#example_in Examples/MonadTransformers/Do.lean countSevenFor}}
```
```output info
{{#example_out Examples/MonadTransformers/Do.lean countSevenFor}}
```

The `for ... in ... do ...` syntax desugars to the use of a type class called `ForIn`, which is a somewhat more complicated version of `ForM` that keeps track of state and early termination.
The standard library provides an adapter that converts a `ForM` instance into a `ForIn` instance, called `ForM.forIn`.
To enable `for` loops based on a `ForM` instance, add something like the following, with appropriate replacements for `AllLessThan` and `Nat`:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean ForInIOAllLessThan}}
```
Note, however, that this adapter only works for `ForM` instances that keep the monad unconstrained, as most of them do.
This is because the adapter uses `StateT` and `ExceptT`, rather than the underlying monad.

Early return is supported in `for` loops.
The translation of `do` blocks with early return into a use of an exception monad transformer applies equally well underneath `forM` as the earlier use of `OptionT` to halt iteration does.
This version of `List.find?` makes use of both:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean findHuh}}
```

In addition to `break`, `for` loops support `continue` to skip the rest of the loop body in an iteration.
An alternative (but confusing) formulation of `List.find?` skips elements that don't satisfy the check:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean findHuhCont}}
```

A `Range` is a structure that consists of a starting number, an ending number, and a step.
They represent a sequence of natural numbers, from the starting number to the ending number, increasing by the step each time.
Lean has special syntax to construct ranges, consisting of square brackets, numbers, and colons that comes in four varieties.
The stopping point must always be provided, while the start and the step are optional, defaulting to `0` and `1`, respectively:

| Expression | Start      | Stop       | Step | As List |
|------------|------------|------------|------|---------|
| `[:10]` | `0` | `10` | `1` | `{{#example_out Examples/MonadTransformers/Do.lean rangeStopContents}}` |
| `[2:10]` | `2` | `10` | `1` | `{{#example_out Examples/MonadTransformers/Do.lean rangeStartStopContents}}` |
| `[:10:3]` | `0` | `10` | `3` | `{{#example_out Examples/MonadTransformers/Do.lean rangeStopStepContents}}` |
| `[2:10:3]` | `2` | `10` | `3` | `{{#example_out Examples/MonadTransformers/Do.lean rangeStartStopStepContents}}` |

Note that the starting number _is_ included in the range, while the stopping numbers is not.
All three arguments are `Nat`s, which means that ranges cannot count down—a range where the starting number is greater than or equal to the stopping number simply contains no numbers.

Ranges can be used with `for` loops to draw numbers from the range.
This program counts even numbers from four to eight:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean fourToEight}}
```
Running it yields:
```output info
{{#example_out Examples/MonadTransformers/Do.lean fourToEightOut}}
```


Finally, `for` loops support iterating over multiple collections in parallel, by separating the `in` clauses with commas.
Looping halts when the first collection runs out of elements, so the declaration:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean parallelLoop}}
```
produces three lines of output:
```lean
{{#example_in Examples/MonadTransformers/Do.lean parallelLoopOut}}
```
```output info
{{#example_out Examples/MonadTransformers/Do.lean parallelLoopOut}}
```

## Mutable Variables

In addition to early `return`, `else`-less `if`, and `for` loops, Lean supports local mutable variables within a `do` block.
Behind the scenes, these mutable variables desugar to code that's equivalent to `StateT`, rather than being implemented by true mutable variables.
Once again, functional programming is used to simulate imperative programming.

A local mutable variable is introduced with `let mut` instead of plain `let`.
The definition `two`, which uses the identity monad `Id` to enable `do`-syntax without introducing any effects, counts to `2`:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean two}}
```
This code is equivalent to a definition that uses `StateT` to add `1` twice:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean twoStateT}}
```

Local mutable variables work well with all the other features of `do`-notation that provide convenient syntax for monad transformers.
The definition `three` counts the number of entries in a three-entry list:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean three}}
```
Similarly, `six` adds the entries in a list:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean six}}
```

`List.count` counts the number of entries in a list that satisfy some check:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean ListCount}}
```

Local mutable variables can be more convenient to use and easier to read than an explicit local use of `StateT`.
However, they don't have the full power of unrestricted mutable variables from imperative languages.
In particular, they can only be modified in the `do`-block in which they are introduced.
This means, for instance, that `for`-loops can't be replaced by otherwise-equivalent recursive helper functions.
This version of `List.count`:
```lean
{{#example_in Examples/MonadTransformers/Do.lean nonLocalMut}}
```
yields the following error on the attempted mutation of `found`:
```output info
{{#example_out Examples/MonadTransformers/Do.lean nonLocalMut}}
```
This is because the recursive function is written in the identity monad, and only the monad of the `do`-block in which the variable is introduced is transformed with `StateT`.

## What counts as a `do` block?

Many features of `do`-notation apply only to a single `do`-block.
Early return terminates the current block, and mutable variables can only be mutated in the block that they are defined in.
To use them effectively, it's important to know what counts as "the same block".

Generally speaking, the indented block following the `do` keyword counts as a block, and the immediate sequence of statements underneath it are part of that block.
Statements in independent blocks that are nonetheless contained in a block are not considered part of the block.
However, the rules that govern what exactly counts as the same block are slightly subtle, so some examples are in order.
The precise nature of the rules can be tested by setting up a program with a mutable variable and seeing where the mutation is allowed.
This program has a mutation that is clearly in the same block as the mutable variable:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean sameBlock}}
```

When a mutation occurs in a `do`-block that is part of a `let`-statement that defines a name using `:=`, then it is not considered to be part of the block:
```lean
{{#example_in Examples/MonadTransformers/Do.lean letBodyNotBlock}}
```
```output error
{{#example_out Examples/MonadTransformers/Do.lean letBodyNotBlock}}
```
However, a `do`-block that occurs under a `let`-statement that defines a name using `←` is considered part of the surrounding block.
The following program is accepted:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean letBodyArrBlock}}
```

Similarly, `do`-blocks that occur as arguments to functions are independent of their surrounding blocks.
The following program is not accepted:
```lean
{{#example_in Examples/MonadTransformers/Do.lean funArgNotBlock}}
```
```output error
{{#example_out Examples/MonadTransformers/Do.lean funArgNotBlock}}
```

If the `do` keyword is completely redundant, then it does not introduce a new block.
This program is accepted, and is equivalent to the first one in this section:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean collapsedBlock}}
```

The contents of branches under a `do` (such as those introduced by `match` or `if`) are considered to be part of the surrounding block, whether or not a redundant `do` is added.
The following programs are all accepted:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean ifDoSame}}

{{#example_decl Examples/MonadTransformers/Do.lean ifDoDoSame}}

{{#example_decl Examples/MonadTransformers/Do.lean matchDoSame}}

{{#example_decl Examples/MonadTransformers/Do.lean matchDoDoSame}}
```
Similarly, the `do` that occurs as part of the `for` and `unless` syntax is just part of their syntax, and does not introduce a fresh `do`-block.
These programs are also accepted:
```lean
{{#example_decl Examples/MonadTransformers/Do.lean doForSame}}

{{#example_decl Examples/MonadTransformers/Do.lean doUnlessSame}}
```


## Imperative or Functional Programming?

The imperative features provided by Lean's `do`-notation allow many programs to very closely resemble their counterparts in languages like Rust, Java, or C#.
This resemblance is very convenient when translating an imperative algorithm into Lean, and some tasks are just most naturally thought of imperatively.
The introduction of monads and monad transformers enables imperative programs to be written in purely functional languages, and `do`-notation as a specialized syntax for monads (potentially locally transformed) allows functional programmers to have the best of both worlds: the strong reasoning principles afforded by immutability and a tight control over available effects through the type system are combined with syntax and libraries that allow programs that use effects to look familiar and be easy to read.
Monads and monad transformers allow functional versus imperative programming to be a matter of perspective.


## Exercises

 * Rewrite `doug` to use `for` instead of the `doList` function. Are there other opportunities to use the features introduced in this section to improve the code? If so, use them!

