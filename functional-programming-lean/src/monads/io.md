# The IO Monad

`IO` as a monad can be understood from two perspectives, which were described in the section on [running programs](../hello-world/running-a-program.md).
Each can help to understand the meanings of `pure` and `bind` for `IO`.

From the first perspective, an `IO` action is an instruction to Lean's run-time system.
For example, the instruction might be "read a string from this file descriptor, then re-invoke the pure Lean code with the string".
This perspective is an _exterior_ one, viewing the program from the perspective of the operating system.
In this case, `pure` is an `IO` action that does not request any effects from the RTS, and `bind` instructs the RTS to first carry out one potentially-effectful operation and then invoke the rest of the program with the resulting value.

From the second perspective, an `IO` action transforms the whole world.
`IO` actions are actually pure, because they receive a unique world as an argument and then return the changed world.
This perspective is an _interior_ one that matches how `IO` is represented inside of Lean.
The world is represented in Lean as a token, and the `IO` monad is structured to make sure that each token is used exactly once.

To see how this works, it can be helpful to peel back one definition at a time.
The `#print` command reveals the internals of Lean datatypes and definitions.
For example,
```lean
{{#example_in Examples/Monads/IO.lean printNat}}
```
results in
```output info
{{#example_out Examples/Monads/IO.lean printNat}}
```
and
```lean
{{#example_in Examples/Monads/IO.lean printCharIsAlpha}}
```
results in
```output info
{{#example_out Examples/Monads/IO.lean printCharIsAlpha}}
```

Sometimes, the output of `#print` includes Lean features that have not yet been presented in this book.
For example,
```lean
{{#example_in Examples/Monads/IO.lean printListIsEmpty}}
```
produces
```output info
{{#example_out Examples/Monads/IO.lean printListIsEmpty}}
```
which includes a `.{u}` after the definition's name, and annotates types as `Type u` rather than just `Type`.
This can be safely ignored for now.

Printing the definition of `IO` shows that it's defined in terms of simpler structures:
```lean
{{#example_in Examples/Monads/IO.lean printIO}}
```
```output info
{{#example_out Examples/Monads/IO.lean printIO}}
```
`IO.Error` represents all the errors that could be thrown by an `IO` action:
```lean
{{#example_in Examples/Monads/IO.lean printIOError}}
```
```output info
{{#example_out Examples/Monads/IO.lean printIOError}}
```
`EIO ε α` represents `IO` actions that will either terminate with an error of type `ε` or succeed with a value of type `α`.
This means that, like the `Except ε` monad, the `IO` monad includes the ability to define error handling and exceptions.

Peeling back another layer, `EIO` is itself defined in terms of a simpler structure:
```lean
{{#example_in Examples/Monads/IO.lean printEIO}}
```
```output info
{{#example_out Examples/Monads/IO.lean printEIO}}
```
The `EStateM` monad includes both errors and state - it's a combination of `Except` and `State`.
It is defined using another type, `EStateM.Result`:
```lean
{{#example_in Examples/Monads/IO.lean printEStateM}}
```
```output info
{{#example_out Examples/Monads/IO.lean printEStateM}}
```
In other words, a program with type `EStateM ε σ α` is a function that accepts an initial state of type `σ` and returns an `EStateM.Result ε σ α`.

`EStateM.Result` is very much like the definition of `Except`, with one constructor that indicates a successful termination and one constructor that indicates an error:
```lean
{{#example_in Examples/Monads/IO.lean printEStateMResult}}
```
```output info
{{#example_out Examples/Monads/IO.lean printEStateMResult}}
```
Just like `Except ε α`, the `ok` constructor includes a result of type `α`, and the `error` constructor includes an exception of type `ε`.
Unlike `Except`, both constructors have an additional state field that includes the final state of the computation.

The `Monad` instance for `EStateM ε σ` requires `pure` and `bind`.
Just as with `State`, the implementation of `pure` for `EStateM` accepts an initial state and returns it unchanged, and just as with `Except`, it returns its argument in the `ok` constructor:
```lean
{{#example_in Examples/Monads/IO.lean printEStateMpure}}
```
```output info
{{#example_out Examples/Monads/IO.lean printEStateMpure}}
```
`protected` means that the full name `EStateM.pure` is needed even if the `EStateM` namespace has been opened.

Similarly, `bind` for `EStateM` takes an initial state as an argument.
It passes this initial state to its first action.
Like `bind` for `Except`, it then checks whether the result is an error.
If so, the error is returned unchanged and the second argument to `bind` remains unused.
If the result was a success, then the second argument is applied to both the returned value and to the resulting state.
```lean
{{#example_in Examples/Monads/IO.lean printEStateMbind}}
```
```output info
{{#example_out Examples/Monads/IO.lean printEStateMbind}}
```

Putting all of this together, `IO` is a monad that tracks state and errors at the same time.
The collection of available errors is that given by the datatype `IO.Error`, which has constructors that describe many things that can go wrong in a program.
The state is a type that represents the real world, called `IO.RealWorld`.
Each basic `IO` action receives this real world and returns another one, paired either with an error or a result.
In `IO`, `pure` returns the world unchanged, while `bind` passes the modified world from one action into the next action.

Because the entire universe doesn't fit in a computer's memory, the world being passed around is just a representation.
So long as world tokens are not re-used, the representation is safe.
This means that world tokens do not need to contain any data at all:
```lean
{{#example_in Examples/Monads/IO.lean printRealWorld}}
```
```output info
{{#example_out Examples/Monads/IO.lean printRealWorld}}
```
