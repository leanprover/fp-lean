# A Monad Construction Kit

`ReaderT` is far from the only useful monad transformer.
This section describes a number of additional transformers.
Each monad transformer consists of the following:
 1. A definition or datatype `T` that takes a monad as an argument.
    It should have a type like `(Type u → Type v) → Type u → Type v`, though it may accept additional arguments prior to the monad.
 2. A `Monad` instance for `T m` that relies on an instance of `Monad m`. This enables the transformed monad to be used as a monad.
 3. A `MonadLift` instance that translates actions of type `m α` into actions of type `T m α`, for arbitrary monads `m`. This enables actions from the underlying monad to be used in the transformed monad.

Furthermore, the `Monad` instance for the transformer should obey the contract for `Monad`, at least if the underlying `Monad` instance does.
In addition, `monadLift (pure x)` should be equivalent to `pure x` in the transformed monad, and `monadLift` should distribute over `bind` so that `monadLift (x >>= f)` is the same as `monadLift x >>= fun y => monadLift (f y)`.

Many monad transformers additionally define type classes in the style of `MonadReader` that describe the actual effects available in the monad.
This can provide more flexibility: it allows programs to be written that rely only on an interface, and don't constrain the underlying monad to be implemented by a given transformer.
The type classes are a way for programs to express their requirements, and monad transformers are a convenient way to meet these requirements.


## Failure with `OptionT`

Failure, represented by the `Option` monad, and exceptions, represented by the `Except` monad, both have corresponding transformers.
In the case of `Option`, failure can be added to a monad by having it contain values of type `Option α` where it would otherwise contain values of type `α`.
For example, `IO (Option α)` represents `IO` actions that don't always return a value of type `α`.
This suggests the definition of the monad transformer `OptionT`:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean OptionTdef}}
```

An example of `OptionT` in action, consider a program that asks the user questions.
The function `getSomeInput` asks for a line of input and removes whitespace from both ends.
If the resulting trimmed input is non-empty, then it is returned, but the function fails if there are no non-whitespace characters:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean getSomeInput}}
```
This particular application tracks users with their name and their favorite species of beetle:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean UserInfo}}
```
Asking the user for input is no more verbose than a function that uses only `IO` would be:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean getUserInfo}}
```
However, because the function runs in an `OptionT IO` context rather than just in `IO`, failure in the first call to `getSomeInput` causes the whole `getUserInfo` to fail, with control never reaching the question about beetles.
The main function, `interact`, invokes `getUserInfo` in a purely `IO` context, which allows it to check whether the call succeeded or failed by matching on the inner `Option`:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean interact}}
```

### The Monad Instance

Writing the monad instance reveals a difficulty.
Based on the types, `pure` should use `pure` from the underlying monad `m` together with `some`.
Just as `bind` for `Option` branches on the first argument, propagating `none`, `bind` for `OptionT` should run the monadic action that makes up the first argument, branch on the result, and then propagate `none`.
Following this sketch yields the following definition, which Lean does not accept:
```lean
{{#example_in Examples/MonadTransformers/Defs.lean firstMonadOptionT}}
```
The error message shows a cryptic type mismatch:
```output error
{{#example_out Examples/MonadTransformers/Defs.lean firstMonadOptionT}}
```
The problem here is that Lean is selecting the wrong `Monad` instance for the surrounding use of `pure`.
Similar errors occur for the definition of `bind`.
One solution is to use type annotations to guide Lean to the correct `Monad` instance:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean MonadOptionTAnnots}}
```
While this solution works, it is inelegant and the code becomes a bit noisy.

An alternative solution is to define functions whose type signatures guide Lean to the correct instances.
In fact, `OptionT` could have been defined as a structure:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean OptionTStructure}}
```
This would solve the problem, because the constructor `OptionT.mk` and the field accessor `OptionT.run` would guide type class inference to the correct instances.
The downside to doing this is that structure values would need to be allocated and deallocated repeatedly when running code that uses it, while the direct definition is a compile-time-only feature.
The best of both worlds can be achieved by defining functions that serve the same role as `OptionT.mk` and `OptionT.run`, but that work with the direct definition:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean FakeStructOptionT}}
```
Both functions return their inputs unchanged, but they indicate the boundary between code that is intended to present the interface of `OptionT` and code that is intended to present the interface of the underlying monad `m`.
Using these helpers, the `Monad` instance becomes more readable:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean MonadOptionTFakeStruct}}
```
Here, the use of `OptionT.mk` indicates that its arguments should be considered as code that uses the interface of `m`, which allows Lean to select the correct `Monad` instances.

After defining the monad instance, it's a good idea to check that the monad contract is satisfied.
The first step is to show that `bind (pure v) f` is the same as `f v`.
Here's the steps:
{{#equations Examples/MonadTransformers/Defs.lean OptionTFirstLaw}}

The second rules states that `bind w pure` is the same as `w`.
To demonstrate this, unfold the definitions of `bind` and `pure`, yielding:
```lean
OptionT.mk do
    match ← w with
    | none => pure none
    | some v => pure (some v)
```
In this pattern match, the result of both cases is the same as the pattern being matched, just with `pure` around it.
In other words, it is equivalent to `w >>= fun y => pure y`, which is an instance of `m`'s second monad rule.

The final rule states that `bind (bind v f) g`  is the same as `bind v (fun x => bind (f x) g)`.
It can be checked in the same way, by expanding the definitions of `bind` and `pure` and then delegating to the underlying monad `m`.

### An `Alternative` Instance

One convenient way to use `OptionT` is through the `Alternative` type class.
Successful return is already indicated by `pure`, and the `failure` and `orElse` methods of `Alternative` provide a way to write a program that returns the first successful result from a number of subprograms:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean AlternativeOptionT}}
```


### Lifting

Lifting an action from `m` to `OptionT m` only requires wrapping `some` around the result of the computation:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean LiftOptionT}}
```


## Exceptions

The monad transformer version of `Except` is very similar to the monad transformer version of `Option`.
Adding exceptions of type `ε` to some monadic action of type `m α` can be accomplished by adding exceptions to `α`, yielding type `m (Except ε α)`:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean ExceptT}}
```
`OptionT` provides `mk` and `run` functions to guide the type checker towards the correct `Monad` instances.
This trick is also useful for `ExceptT`:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean ExceptTFakeStruct}}
```
The `Monad` instance for `ExceptT` is also very similar to the instance for `OptionT`.
The only difference is that it propagates a specific error value, rather than `none`:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean MonadExceptT}}
```

The type signatures of `ExceptT.mk` and `ExceptT.run` contain a subtle detail: they annotate the universe levels of `α` and `ε` explicitly.
If they are not explicitly annotated, then Lean generates a more general type signature in which they have distinct polymorphic universe variables.
However, the definition of `ExceptT` expects them to be in the same universe, because they can both be provided as arguments to `m`.
This can lead to a problem in the `Monad` instance where the universe level solver fails to find a working solution:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean ExceptTNoUnis}}

{{#example_in Examples/MonadTransformers/Defs.lean MonadMissingUni}}
```
```output error
{{#example_out Examples/MonadTransformers/Defs.lean MonadMissingUni}}
```
This kind of error message is typically caused by underconstrained universe variables.
Diagnosing it can be tricky, but a good first step is to look for reused universe variables in some definitions that are not reused in others.

Unlike `Option`, the `Except` datatype is typically not used as a data structure.
It is always used as a control structure with its `Monad` instance.
This means that it is reasonable to lift `Except ε` actions into `ExceptT ε m`, as well as actions from the underlying monad `m`.
Lifting `Except` actions into `ExceptT` actions is done by wrapping them in `m`'s `pure`, because an action that only has exception effects cannot have any effects from the monad `m`:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean ExceptTLiftExcept}}
```
Because actions from `m` do not have any exceptions in them, their value should be wrapped in `Except.ok`.
This can be accomplished using the fact that `Functor` is a superclass of `Monad`, so applying a function to the result of any monadic computation can be accomplished using `Functor.map`:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean ExceptTLiftM}}
```

### Type Classes for Exceptions

Exception handling fundamentally consists of two operations: the ability to throw exceptions, and the ability to recover from them.
Thus far, this has been accomplished using the constructors of `Except` and pattern matching, respectively.
However, this ties a program that uses exceptions to one specific encoding of the exception handling effect.
Using a type class to capture these operations allows a program that uses exceptions to be used in _any_ monad that supports throwing and catching.

Throwing an exception should take an exception as an argument, and it should be allowed in any context where a monadic action is requested.
The "any context" part of the specification can be written as a type by writing `m α`—because there's no way to produce a value of any arbitrary type, the `throw` operation must be doing something that causes control to leave that part of the program.
Catching an exception should accept any monadic action together with a handler, and the handler should explain how to get back to the action's type from an exception:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean MonadExcept}}
```

The universe levels on `MonadExcept` differ from those of `ExceptT`.
In `ExceptT`, both `ε` and `α` have the same level, while `MonadExcept` imposes no such limitation.
This is because `MonadExcept` never places an exception value inside of `m`.
The most general universe signature recognizes the fact that `ε` and `α` are completely independent in this definition.
Being more general means that the type class can be instantiated for a wider variety of types.

An example program that uses `MonadExcept` is a simple division service.
The program is divided into two parts: a frontend that supplies a user interface based on strings that handles errors, and a backend that actually does the division.
Both the frontend and the backend can throw exceptions, the former for ill-formed input and the latter for division by zero errors.
The exceptions are an inductive type:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean ErrEx}}
```
The backend checks for zero, and divides if it can:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean divBackend}}
```
The frontend's helper `asNumber` throws an exception if the string it is passed is not a number.
The overall frontend converts its inputs to `Int`s and calls the backend, handling exceptions by returning a friendly string error:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean asNumber}}

{{#example_decl Examples/MonadTransformers/Defs.lean divFrontend}}
```
Throwing and catching exceptions is common enough that Lean provides a special syntax for using `MonadExcept`.
Just as `+` is short for `HAdd.hAdd`, `try` and `catch` can be used as shorthand for the `tryCatch` method:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean divFrontendSugary}}
```

In addition to `Except` and `ExceptT`, there are useful `MonadExcept` instances for other types that may not seem like exceptions at first glance.
For example, failure due to `Option` can be seen as throwing an exception that contains no data whatsoever, so there is an instance of `{{#example_out Examples/MonadTransformers/Defs.lean OptionExcept}}` that allows `try ... catch ...` syntax to be used with `Option`.

## State

A simulation of mutable state is added to a monad by having monadic actions accept a starting state as an argument and return a final state together with their result.
The bind operator for a state monad provides the final state of one action as an argument to the next action, threading the state through the program.
This pattern can also be expressed as a monad transformer:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean DefStateT}}
```


Once again, the monad instance is very similar to that for `State`.
The only difference is that the input and output states are passed around and returned in the underlying monad, rather than with pure code:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean MonadStateT}}
```

The corresponding type class has `get` and `set` methods.
One downside of `get` and `set` is that it becomes too easy to `set` the wrong state when updating it.
This is because retrieving the state, updating it, and saving the updated state is a natural way to write some programs.
For example, the following program counts the number of diacritic-free English vowels and consonants in a string of letters:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean countLetters}}
```
It would be very easy to write `set st` instead of `set st'`.
In a large program, this kind of mistake can lead to difficult-to-diagnose bugs.

While using a nested action for the call to `get` would solve this problem, it can't solve all such problems.
For example, a function might update a field on a structure based on the values of two other fields.
This would require two separate nested-action calls to `get`.
Because the Lean compiler contains optimizations that are only effective when there is a single reference to a value, duplicating the references to the state might lead to code that is significantly slower.
Both the potential performance problem and the potential bug can be worked around by using `modify`, which transforms the state using a function:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean countLettersModify}}
```
The type class contains a function akin to `modify` called `modifyGet`, which allows the function to both compute a return value and transform an old state in a single step.
The function returns a pair in which the first element is the return value, and the second element is the new state; `modify` just adds the constructor of `Unit` to the pair used in `modifyGet`:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean modify}}
```

The definition of `MonadState` is as follows:
```lean
{{#example_decl Examples/MonadTransformers/Defs.lean MonadState}}
```
`PUnit` is a version of the `Unit` type that is universe-polymorphic to allow it to be in `Type u` instead of `Type`.
While it would be possible to provide a default implementation of `modifyGet` in terms of `get` and `set`, it would not admit the optimizations that make `modifyGet` useful in the first place, rendering the method useless.

## `Of` Classes and `The` Functions

Thus far, each monad type class that takes extra information, like the type of exceptions for `MonadExcept` or the type of the state for `MonadState`, has this type of extra information as an output parameter.
For simple programs, this is generally convenient, because a monad that combines one use each of `StateT`, `ReaderT`, and `ExceptT` has only a single state type, environment type, and exception type.
As monads grow in complexity, however, they may involve multiple states or errors types.
In this case, the use of an output parameter makes it impossible to target both states in the same `do`-block.

For these cases, there are additional type classes in which the extra information is not an output parameter.
These versions of the type classes use the word `Of` in the name.
For example, `MonadStateOf` is like `MonadState`, but without an `outParam` modifier.

Similarly, there are versions of the type class methods that accept the type of the extra information as an _explicit_, rather than implicit, argument.
For `MonadStateOf`, there are `{{#example_in Examples/MonadTransformers/Defs.lean getTheType}}` with type
```lean
{{#example_out Examples/MonadTransformers/Defs.lean getTheType}}
```
and `{{#example_in Examples/MonadTransformers/Defs.lean modifyTheType}}` with type
```lean
{{#example_out Examples/MonadTransformers/Defs.lean modifyTheType}}
```
There is no `setThe` because the type of the new state is enough to decide which surrounding state monad transformer to use.

In the Lean standard library, there are instances of the non-`Of` versions of the classes defined in terms of the instances of the versions with `Of`.
In other words, implementing the `Of` version yields implementations of both.
It's generally a good idea to implement the `Of` version, and then start writing programs using the non-`Of` versions of the class, transitioning to the `Of` version if the output parameter becomes inconvenient.

## Transformers and `Id`

The identity monad `Id` is the monad that has no effects whatsoever, to be used in contexts that expect a monad for some reason but where none is actually necessary.
Another use of `Id` is to serve as the bottom of a stack of monad transformers.
For instance, `StateT σ Id` works just like `State σ`.


## Exercises

### Monad Contract

Using pencil and paper, check that the rules of the monad transformer contract are satisfied for each monad transformer in this section.

### Logging Transformer

Define a monad transformer version of `WithLog`.
Also define the corresponding type class `MonadWithLog`, and write a program that combines logging and exceptions.

### Counting Files

Modify `doug`'s monad with `StateT` such that it counts the number of directories and files seen.
At the end of execution, it should display a report like:
```
  Viewed 38 files in 5 directories.
```
