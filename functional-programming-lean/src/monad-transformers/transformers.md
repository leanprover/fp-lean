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
These concerns yield the following definition, which Lean does not accept:
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
While this solution works, the code becomes a bit noise.

An alternative solution is to define functions whose type signatures guides Lean to the correct instances.
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



## State

## Transformers and `Id`

## Order Matters

Here show the difference between StateT Except and ExceptT State, and argue both that it's a strength and a limitation so readers can understand fully and make up their own minds

Show correctness pitfalls of MTL-style programs that rely on the right order
