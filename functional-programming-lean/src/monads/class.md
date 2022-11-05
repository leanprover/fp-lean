# The Monad Type Class

Rather than having to import an operator like `ok` or `andThen` for each type that is a monad, the Lean standard library contains type classes that allow them to be overloaded, so that the same operators can be used for _any_ monad.
Monads have two operations, which are the equivalent of `ok` and `andThen`:
```lean
{{#example_decl Examples/Monads/Class.lean FakeMonad}}
```
This definition is slightly simplified.
The actual definition in the Lean library is somewhat more involved, and will be presented later.

As an example, `firstThirdFifthSeventh` was defined separately for `Option α` and `Err String α` return types.
Now, it can be defined polymorphically for _any_ monad.
It does, however, require a lookup function as an argument, because different monads might fail to find a result in different ways.
The infix argument for `bind` is `>>=`, which plays the same role as `~~>` in the examples.
```lean
{{#example_decl Examples/Monads/Class.lean firstThirdFifthSeventhMonad}}
```



## The Monad Contract
Just as every pair of instances of `BEq` and `Hashable` should ensure that any two equal values have the same hash, there is a contract that each instance of `Monad` should obey.
First, `pure` should be a left identity of `bind`.
That is, `bind (pure v) f` should be the same as `f v`.
Secondly, `pure` should be a right identity of `bind`, so `bind v pure` is the same as `v`.
Finally, `bind` should be associative, so `bind (bind v f) g` is the same as `bind v (fun x => bind (f x) g)`.

