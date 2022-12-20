# The Applicative Contract

Just like fuctors, monads, and types that implement `BEq` and `Hashable`, `Applicative` has a set of rules that all instances should adhere to.

There are four rules that an applicative functor should follow:
1. It should respect identity, so `pure id <*> v = v`
2. It should respect function composition, so `pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`
3. Sequencing pure operations should be a no-op, so `pure f <*> pure x = pure (f x)`
4. The ordering of pure operations doesn't matter, so `u <*> pure x = pure (fun f => f x) <*> u`

To check these for the `Applicative Option` instance, start by expanding `pure` into `some`.

The first rule states that `some id <*> v = v`.
The definition of `seq` for `Option` states that this is the same as `id <$> v = v`, which is one of the `Functor` rules that have already been checked.

The second rule states that `some (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`.
If any of `u`, `v`, or `w` is `none`, then both sides are `none`, so the property holds.
Assuming that `u` is `some f`, that `v` is `some g`, and that `w` is `some x`, then this is equivalent to saying that `some (· ∘ ·) <*> some f <*> some g <*> some x = some f <*> (some g <*> some x)`.
Evaluating the two sides yields the same result:
```lean
{{#example_eval Examples/FunctorApplicativeMonad.lean OptionHomomorphism1}}

{{#example_eval Examples/FunctorApplicativeMonad.lean OptionHomomorphism2}}
```

The third rule follows directly from the definition of `seq`:
```lean
{{#example_eval Examples/FunctorApplicativeMonad.lean OptionPureSeq}}
```

In the fourth case, assume that `u` is `some f`, because if it's `none`, both sides of the equation are `none`.
`some f <*> some x` evaluates directly to `some (f x)`, as does `some (fun g => g x) <*> some f`.


## All Applicatives are Functors

The two operators for `Applicative` are enough to define `map`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ApplicativeMap}}
```

This can only be used to implement `Functor` if the contract for `Applicative` guarantees the contract for `Functor`, however.
The first rule of `Functor` is that `id <$> x = x`, which follows directly from the first rule for `Applicative`.
The second rule of `Functor` is that `map (f ∘ g) x = map f (map g x)`.
Unfolding the definition of `map` here results in `pure (f ∘ g) <*> x = pure f <*> (pure g <*> x)`.
Using the rule that sequencing pure operations is a no-op, the left side can be rewritten to `pure (· ∘ ·) <*> pure f <*> pure g <*> x`.
This is an instance of the rule that states that applicative functors respect function composition.

This justifies a definition of `Applicative` that extends `Functor`, with a default definition of `map` given in terms of `pure` and `seq`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ApplicativeExtendsFunctorOne}}
```

## All Monads are Applicative Functors

An instance of `Monad` already requires an implementation of `pure`.
Together with `bind`, this is enough to define `seq`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean MonadSeq}}
```
Once again, checking that the `Monad` contract implies the `Applicative` contract will allow this to be used as a default definition for `seq` if `Monad` extends `Applicative`.

The rest of this section consists of an argument that this implementation of `seq` based on `bind` in fact satisfies the `Applicative` contract.
One of the beautiful things about functional programming is that this kind of argument can be worked out on a piece of paper with a pencil, using the kinds of evaluation rules from [the initial section on evaluating expressions](../getting-to-know/evaluating.md).
Thinking about the meanings of the operations while reading these arguments can sometimes help with understanding; however, please feel free to skip them the first time through if they get overwhelming.

Replacing `do`-notation with explicit uses of `>>=` makes it easier to apply the `Monad` rules:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean MonadSeqDesugar}}
```


To check that this definition respects identity, check that `seq (pure id) (fun ⟨⟩ => v) = v`.
The left hand side is equivalent to `pure id >>= fun g => (fun ⟨⟩ => v) ⟨⟩ >>= fun y => pure (g y)`.
The unit function in the middle can be eliminated immediately, yielding `pure id >>= fun g => v >>= fun y => pure (g y)`.
Using the fact that `pure` is a left identity of `>>=`, this is the same as `v >>= fun y => pure (id y)`, which is `v >>= fun y => pure y`.
Because `fun x => f x` is the same as `f`, this is the same as `v >>= pure`, and the fact that `pure` is a right identity of `>>=` can be used to get `v`.

This kind of informal reasoning can be made easier to read with a bit of reformatting.
In the following chart, read "EXPR1 ={ REASON }= EXPR2" as "EXPR1 is the same as EXPR2 because REASON":
{{#equations Examples/FunctorApplicativeMonad.lean mSeqRespId}}


To check that it respects function composition, check that `pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`.
The first step is to replace `<*>` with this definition of `seq`.
After that, a (somewhat long) series of steps that use the identity and associativity rules from the `Monad` contract is enough to get from one to the other:
{{#equations Examples/FunctorApplicativeMonad.lean mSeqRespComp}}

To check that sequencing pure operations is a no-op:
{{#equations Examples/FunctorApplicativeMonad.lean mSeqPureNoOp}}

And finally, to check that the ordering of pure operations doesn't matter:
{{#equations Examples/FunctorApplicativeMonad.lean mSeqPureNoOrder}}

This justifies a definition of `Monad` that extends `Applicative`, with a default definition of `seq`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean MonadExtends}}
```
`Applicative`'s own default definition of `map` means that every `Monad` instance automatically generates `Applicative` and `Functor` instances as well.

