# The Monad Type Class

Rather than having to import an operator like `ok` or `andThen` for each type that is a monad, the Lean standard library contains a type class that allow them to be overloaded, so that the same operators can be used for _any_ monad.
Monads have two operations, which are the equivalent of `ok` and `andThen`:
```lean
{{#example_decl Examples/Monads/Class.lean FakeMonad}}
```
This definition is slightly simplified.
The actual definition in the Lean library is somewhat more involved, and will be presented later.

The `Monad` instances for `Option` and `Except` can be created by adapting the definitions of their respective `andThen` operations:
```lean
{{#example_decl Examples/Monads/Class.lean MonadOptionExcept}}
```

As an example, `firstThirdFifthSeventh` was defined separately for `Option α` and `Except String α` return types.
Now, it can be defined polymorphically for _any_ monad.
It does, however, require a lookup function as an argument, because different monads might fail to find a result in different ways.
The infix version of `bind` is `>>=`, which plays the same role as `~~>` in the examples.
```lean
{{#example_decl Examples/Monads/Class.lean firstThirdFifthSeventhMonad}}
```

Given example lists of slow mammals and fast birds, this implementation of `firstThirdFifthSeventh` can be used with `Option`:
```lean
{{#example_decl Examples/Monads/Class.lean animals}}

{{#example_in Examples/Monads/Class.lean noneSlow}}
```
```output info
{{#example_out Examples/Monads/Class.lean noneSlow}}
```
```lean
{{#example_in Examples/Monads/Class.lean someFast}}
```
```output info
{{#example_out Examples/Monads/Class.lean someFast}}
```

After renaming `Except`'s lookup function `get` to something more specific, the very same  implementation of `firstThirdFifthSeventh` can be used with `Except` as well:
```lean
{{#example_decl Examples/Monads/Class.lean getOrExcept}}

{{#example_in Examples/Monads/Class.lean errorSlow}}
```
```output info
{{#example_out Examples/Monads/Class.lean errorSlow}}
```
```lean
{{#example_in Examples/Monads/Class.lean okFast}}
```
```output info
{{#example_out Examples/Monads/Class.lean okFast}}
```
The fact that `m` must have a `Monad` instance means that the `>>=` and `pure` operations are available.


## General Monad Operations

Because many different types are monads, functions that are polymorphic over _any_ monad are very powerful.
For example, the function `mapM` is a version of `map` that uses a `Monad` to sequence and combine the results of applying a function:
```lean
{{#example_decl Examples/Monads/Class.lean mapM}}
```
The return type of the function argument `f` determines which `Monad` instance will be used.
In other words, `mapM` can be used for functions that produce logs, for functions that can fail, or for functions that use mutable state.
Because `f`'s type determines the available effects, they can be tightly controlled by API designers.

As described in [this chapter's introduction](../monads.md#numbering-tree-nodes), `State σ α` represents programs that make use of a mutable variable of type `σ` and return a value of type `α`.
These programs are actually functions from a starting state to a pair of a value and a final state.
The `Monad` class requires that its parameter expect a single type argument—that is, it should be a `Type → Type`.
This means that the instance for `State` should mention the state type `σ`, which becomes a parameter to the instance:
```lean
{{#example_decl Examples/Monads/Class.lean StateMonad}}
```
This means that the type of the state cannot change between calls to `get` and `set` that are sequenced using `bind`, which is a reasonable rule for stateful computations.
The operator `increment` increases a saved state by a given amount, returning the old value:
```lean
{{#example_decl Examples/Monads/Class.lean increment}}
```

Using `mapM` with `increment` results in a program that computes the sum of the entries in a list.
More specifically, the mutable variable contains the sum so far, while the resulting list contains a running sum.
In other words, `{{#example_in Examples/Monads/Class.lean mapMincrement}}` has type `{{#example_out Examples/Monads/Class.lean mapMincrement}}`, and expanding the definition of `State` yields `{{#example_out Examples/Monads/Class.lean mapMincrement2}}`.
It takes an initial sum as an argument, which should be `0`:
```lean
{{#example_in Examples/Monads/Class.lean mapMincrementOut}}
```
```output info
{{#example_out Examples/Monads/Class.lean mapMincrementOut}}
```

A [logging effect](../monads.md#logging) can be represented using `WithLog`.
Just like `State`, its `Monad` instance is polymorphic with respect to the type of the logged data:
```lean
{{#example_decl Examples/Monads/Class.lean MonadWriter}}
```
`saveIfEven` is a function that logs even numbers but returns its argument unchanged:
```lean
{{#example_decl Examples/Monads/Class.lean saveIfEven}}
```
Using this function with `mapM` results in a log containing even numbers paired with an unchanged input list:
```lean
{{#example_in Examples/Monads/Class.lean mapMsaveIfEven}}
```
```output info
{{#example_out Examples/Monads/Class.lean mapMsaveIfEven}}
```



## The Identity Monad

Monads encode programs with effects, such as failure, exceptions, or logging, into explicit representations as data and functions.
Sometimes, however, an API will be written to use a monad for flexibility, but the API's client may not require any encoded effects.
The _identity monad_ is a monad that has no effects.
It allows pure code to be used with monadic APIs:
```lean
{{#example_decl Examples/Monads/Class.lean IdMonad}}
```
The type of `pure` should be `α → Id α`, but `Id α` reduces to just `α`.
Similarly, the type of `bind` should be `α → (α → Id β) → Id β`.
Because this reduces to `α → (α → β) → β`, the second argument can be applied to the first to find the result.

With the identity monad, `mapM` becomes equivalent to `map`.
To call it this way, however, Lean requires a hint that the intended monad is `Id`:
```lean
{{#example_in Examples/Monads/Class.lean mapMId}}
```
```output info
{{#example_out Examples/Monads/Class.lean mapMId}}
```
Omitting the hint results in an error:
```lean
{{#example_in Examples/Monads/Class.lean mapMIdNoHint}}
```
```output error
{{#example_out Examples/Monads/Class.lean mapMIdNoHint}}
```
In this error, the application of one metavariable to another indicates that Lean doesn't run the type-level computation backwards.
The return type of the function is expected to be the monad applied to some other type.
Similarly, using `mapM` with a function whose type doesn't provide any specific hints about which monad is to be used results in an "instance problem stuck" message:
```lean
{{#example_in Examples/Monads/Class.lean mapMIdId}}
```
```output error
{{#example_out Examples/Monads/Class.lean mapMIdId}}
```


## The Monad Contract
Just as every pair of instances of `BEq` and `Hashable` should ensure that any two equal values have the same hash, there is a contract that each instance of `Monad` should obey.
First, `pure` should be a left identity of `bind`.
That is, `bind (pure v) f` should be the same as `f v`.
Secondly, `pure` should be a right identity of `bind`, so `bind v pure` is the same as `v`.
Finally, `bind` should be associative, so `bind (bind v f) g` is the same as `bind v (fun x => bind (f x) g)`.

This contract specifies the expected properties of programs with effects more generally.
Because `pure` has no effects, sequencing its effects with `bind` shouldn't change the result.
The associative property of `bind` basically says that the sequencing bookkeeping itself doesn't matter, so long as the order in which things are happening is preserved.

## Exercises

### Mapping on a Tree

Define a function `BinTree.mapM`.
By analogy to `mapM` for lists, this function should apply a monadic function to each data entry in a tree, as a preorder traversal.
The type signature should be:
```
def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
```


### The Option Monad Contract

First, write a convincing argument that the `Monad` instance for `Option` satisfies the monad contract.
Then, consider the following instance:
```lean
{{#example_decl Examples/Monads/Class.lean badOptionMonad}}
```
Both methods have the correct type.
Why does this instance violate the monad contract?



