# Applicative Functors

An _applicative functor_ is a functor that has two additional operations available: `pure` and `seq`.
`pure` is the same operator used in `Monad`, because `Monad` in fact inherits from `Applicative`.
`seq` is much like `map`: it allows a function to be used in order to transform the contents of a datatype.
However, with `seq`, the function is itself contained in the datatype: `{{#example_out Examples/FunctorApplicativeMonad.lean seqType}}`.
The second argument has a type that begins with `Unit →` to allow the definition of `seq` to short-circuit.

The value of this short-circuiting behavior can be seen in the instance of `Applicative Option`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ApplicativeOption}}
```
In this case, if there is no function for `seq` to apply, then there is no need to compute its argument.
The same consideration informs the instance of `Applicative` for `Except`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ApplicativeExcept}}
```
This short-circuiting behavior depends only on the `Option` or `Except` structures that _surround_ the function, rather than on the function itself.

Monads can be seen as a way of capturing the notion of sequentially executing statements into a pure functional language.
The result of one statement can affect which further statements run.
This can be seen in the type of `bind`: `{{#example_out Examples/FunctorApplicativeMonad.lean bindType}}`.
The first statement's resulting value is an input into a function that computes the next statement to execute.
Successive uses of `bind` are like a sequence of statements in an imperative programming language, and `bind` is powerful enough to implement control structures like conditionals and loops.

Following this analogy, `Applicative` captures function application in a language that has side effects.
The arguments to a function in languages like Kotlin or C# are evaluated from left to right.
Side effects performed by earlier arguments occur before those performed by later arguments.
A function is not powerful enough to implement custom short-circuiting operators that depend on the specific value of an argument, however.

Typically, `seq` is not invoked directly.
Instead, the operator `<*>` is used.
This operator wraps its second argument in `fun ⟨⟩ => ...`, simplifying the call site.

The key feature that allows `seq` to be used with multiple arguments is that a multiple-argument Lean function is really a single-argument function that returns another function that's waiting for the rest of the arguments.
In other words, if the first argument to `seq` is awaiting multiple arguments, then the result of the `seq` will be awaiting the rest.
For example, `{{#example_in Examples/FunctorApplicativeMonad.lean somePlus}}` can have the type `{{#example_out Examples/FunctorApplicativeMonad.lean somePlus}}`.
Providing one argument, `{{#example_in Examples/FunctorApplicativeMonad.lean somePlusFour}}`, results in the type `{{#example_out Examples/FunctorApplicativeMonad.lean somePlusFour}}`.
This can itself be used with `seq`, so `{{#example_in Examples/FunctorApplicativeMonad.lean somePlusFourSeven}}` has the type `{{#example_out Examples/FunctorApplicativeMonad.lean somePlusFourSeven}}`.

Not every functor is applicative.
`Pair` is like the built-in product type `Prod`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean Pair}}
```
Like `Except`, `{{#example_in Examples/FunctorApplicativeMonad.lean PairType}}` has type `{{#example_out Examples/FunctorApplicativeMonad.lean PairType}}`.
This means that `Pair α` has type `Type → Type`, and a `Functor` instance is possible:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean FunctorPair}}
```
This instance obeys the `Functor` contract.

The two properties to check are that `{{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapId 0}} = {{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapId 2}}` and that `{{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapComp1 0}} = {{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapComp2 0}}`.
The first property can be checked by just stepping through the evaluation of the left side, and noticing that it evaluates to the right side:
```lean
{{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapId}}
```
The second can be checked by stepping through both sides, and noting that they yield the same result:
```lean
{{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapComp1}}

{{#example_eval Examples/FunctorApplicativeMonad.lean checkPairMapComp2}}
```

Attempting to define an `Applicative` instance, however, does not work so well.
It will require a definition of `pure`:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean Pairpure}}
```
```output error
{{#example_out Examples/FunctorApplicativeMonad.lean Pairpure}}
```
There is a value with type `β` in scope (namely `x`), and the error message from the underscore suggests that the next step is to use the constructor `Pair.mk`:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean Pairpure2}}
```
```output error
{{#example_out Examples/FunctorApplicativeMonad.lean Pairpure2}}
```
Unfortunately, there is no `α` available.
Because `pure` would need to work for _all possible types_ α to define an instance of `Applicative (Pair α)`, this is impossible.
After all, a caller could choose `α` to be `Empty`, which has no values at all.


### The Applicative Contract

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
Replacing `do`-notation with explicit uses of `>>=` makes it easier to apply the `Monad` rules:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean MonadSeqDesugar}}
```


To check that this definition respects identity, check that `seq (pure id) (fun ⟨⟩ => v) = v`.
The left hand side is equivalent to `pure id >>= fun g => (fun ⟨⟩ => v) ⟨⟩ >>= fun y => pure (g y)`.
The unit function in the middle can be eliminated immediately, yielding `pure id >>= fun g => v >>= fun y => pure (g y)`.
Using the fact that `pure` is a left identiy of `>>=`, this is the same as `v >>= fun y => pure (id y)`, which is `v >>= fun y => pure y`.
Because `fun x => f x` is the same as `f`, this is the same as `v >>= pure`, and the fact that `pure` is a right identity of `>>=` can be used to get `v`.

To check that it respects function composition, 

## Power vs Flexibility

If the monad abstraction is more powerful than the functor abstraction, why are functors interesting at all?
Increasing the power of an abstraction allows it to be used to write more programs, but it rules out some types that could otherwise implement it.
Programs that are written for `Monad` simply can't be used with types that only can implement `Functor`.
Furthermore, implementations of weaker abstractions have fewer constraints, and can thus choose 


Saying that every monad is a functor means the following:
 * Using `bind` and `pure`, it is possible to implement `map`
 * The three rules in the monad contract guarantee the functor contract
 
 

Key points:

 - Weaker abstractions allow more implementations
 - Every Monad is Applicative, every Applicative is Functor
 - Just because an instance has the right types doesn't mean the law is obeyed
