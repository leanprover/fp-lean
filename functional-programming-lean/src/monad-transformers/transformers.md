# A Monad Construction Kit

Monad transformers add a new effect to an existing monad.
Many interesting monads can be built from the composition of existing monad transformers, removing the obligation to define the monad from scratch.
A monad transformer consists of the following:
 1. A definition or datatype `T` that takes a monad as an argument.
    It should have a type like `(Type u → Type v) → Type u → Type (max u v)`, though it may accept additional arguments prior to the monad.
 2. A `Monad` instance for `T m` that relies on an instance of `Monad m`. This enables the transformed monad to be used as a monad.
 3. A `MonadLift` instance that translates actions of type `m α` into actions of type `T m α`, for arbitrary monads `m`. This enables actions from the underlying monad to be used in the transformed monad.

Furthermore, the `Monad` instance for the transformer should obey the contract for `Monad`, at least if the underlying `Monad` instance does.
In addition, `monadLift (pure x)` should be equivalent to `pure x` in the transformed monad, and `monadLift` should distribute over `bind` so that `monadLift (x >>= f)` is the same as `monadLift x >>= fun y => monadLift (f y)`.

Many monad transformers additionally define type classes that describe the actual effects available in the monad.
This can provide more flexibility: it allows programs to be written that rely only on an interface, and don't constrain the underlying monad to be implemented by a given transformer.
The type classes are a way for programs to express their requirements, and monad transformers are a convenient way to meet these requirements.


## Failure and Exceptions

Failure, represented by the `Option` monad, and exceptions, represented by the `Except` monad, both have corresponding transformers.


## State



## Order Matters

Here show the difference between StateT Except and ExceptT State, and argue both that it's a strength and a limitation so readers can understand fully and make up their own minds

Show correctness pitfalls of MTL-style programs that rely on the right order
