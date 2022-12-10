# Interlude: Functors, Applicative Functors, and Monads

`Functor` and `Monad` have something in common: they both describe operations for types that are still waiting for a type argument.
One way to understand them is that `Functor` describes containers in which the contained data can be transformed, and `Monad` describes an encoding of side effects.
This understanding is incomplete, however.
After all, `Option` has instances for both `Functor` and `Monad`, and simultaneously represents an optional value _and_ a computation that might fail without returning an error message.

It turns out that _every monad is a functor_.
Another way to say this is that the monad abstraction is more powerful than the functor abstraction, because not every functor is a monad.
Furthermore, there is an additional intermediate type class, called _applicative functors_, that has enough power to write many interesting programs.
The type class `Applicative` provides the overloadable operations of applicative functors.
Every monad is an applicative functor, and every applicative functor is a functor, but the converses do not hold.

## Structure Inheritance

In order to understand the full definitions of `Functor`, `Applicative`, and `Monad`, another Lean feature is necessary: structure inheritance.
Structure inheritance allows one structure type to provide the interface of another, along with additional fields.
This can be useful when modeling concepts that have a clear taxonomic relationship.
For example, take a model of mythical creatures.
Some of them are large, and some are small:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean MythicalCreature}}
```
Behind the scenes, defining the `MythicalCreature` structure creates an inductive type with a single constructor called `mk`:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean MythicalCreatureMk}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean MythicalCreatureMk}}
```
Similarly, a function `MythicalCreature.large` is created that actually extracts the field from the constructor:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean MythicalCreatureLarge}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean MythicalCreatureLarge}}
```

In most old stories, each monster can be defeated in some way.
A description of a monster should include this information, along with whether it is large:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean Monster}}
```
The `extends MythicalCreature` in the heading states that every monster is also mythical.
To define a `Monster`, both the fields from `MythicalCreature` and the fields from `Monster` should be provided.
A troll is a large monster that is vulnerable to sunlight:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean troll}}
```

Inheritance is implemented as composition: the constructor `Monster.mk` takes a `MythicalCreature` as its argument:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean MonsterMk}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean MonsterMk}}
```
In addition to defining functions to project each new field, a function `{{#example_in Examples/FunctorApplicativeMonad.lean MonsterToCreature}}` is defined with type `{{#example_out Examples/FunctorApplicativeMonad.lean MonsterToCreature}}`.
This can be used to extract the underlying creature.

Lean's dot notation is capable of taking inheritance into account.
In other words, the existing `MythicalCreature.large` can be used with a `Monster`, and Lean automatically inserts the call to `{{#example_in Examples/FunctorApplicativeMonad.lean MonsterToCreature}}` before the call to `MythicalCreature.large`.
However, this only occurs when using dot notation, and applying the projection function using normal function call syntax results in a type error:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean trollLargeNoDot}}
```
```output error
{{#example_out Examples/FunctorApplicativeMonad.lean trollLargeNoDot}}
```
Dot notation can also take inheritance into account for user-defined functions.
A small creature is one that is not large:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean small}}
```
Evaluating `{{#example_in Examples/FunctorApplicativeMonad.lean smallTroll}}` yields `{{#example_out Examples/FunctorApplicativeMonad.lean smallTroll}}`, while attempting to evaluate `{{#example_in Examples/FunctorApplicativeMonad.lean smallTrollWrong}}` results in:
```output error
{{#example_out Examples/FunctorApplicativeMonad.lean smallTrollWrong}}
```

## Multiple Inheritance

A helper is a mythical creature that can provide assistance when given the correct payment:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean Helper}}
```
For example, a _nisse_ is a kind of small elf that's known to help around the house when provided with tasty porridge:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean elf}}
```

TODO example of multiple inheritance and field overlap

## Type Class Inheritance

Behind the scenes, type classes are structures.
Defining a new type class defines a new structure, and defining an instance creates a value of that structure type.
They are then added to internal tables in Lean that allow it to find the instances upon request.
A consequence of this is that type classes may inherit from other type classes, following all of the rules.

## Applicative Functors

An _applicative functor_ is a functor that has two additional operations available: `pure` and `seq`.
`pure` is the same operator used in `Monad`, because `Monad` in fact inherits from `Applicative`.
`seq` is much like `map`: it allows a function to be used to ... TODO

Not every functor is applicative.



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
