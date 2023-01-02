# Universes

In the interests of simplicity, this book has thus far papered over an important feature of Lean: _universes_.
A universe is a type that classifies other types.
Two of them are familiar: `Type` and `Prop`.
`Type` classifies ordinary types, such as `Nat`, `String`, `Int → String × Char`, and `IO Unit`.
`Prop` classifies propositions that may be true or false, such as `"nisse" = "elf"` or `3 > 2`.
The type of `Prop` is `Type`:
```lean
{{#example_in Examples/Universes.lean PropType}}
```
```output info
{{#example_out Examples/Universes.lean PropType}}
```

For technical reasons, more universes than these two are needed.
In particular, `Type` cannot itself be a `Type`.
This would allow a logical paradox to be constructed and undermine Lean's usefulness as a theorem prover.

The formal argument for this is known as _Girard's Paradox_.
It is a version of a better-known paradox known as _Russell's Paradox_, which was used to show that early versions of set theory were inconsistent.
In these set theories, a set can be defined by a property.
For example, one might have the set of all red things, the set of all fruit, the set of all natural numbers, or even the set of all sets.
Given a set, one can ask whether a given element is contained in it.
For instance, a bluebird is not contained in the set of all red things, but the set of all red things is contained in the set of all sets.
Indeed, the set of all sets even contains itself.

What about the set of all sets that do not contain themselves?
It contains the set of all red things, as the set of all red things is not itself red.
It does not contain the set of all sets, because the set of all sets contains itself.
But does it contain itself?
If it does contain itself, then it cannot contain itself.
But if it does not, then it must.

This is a contradiction, which demonstrates that something was wrong with the initial assumptions.
In particular, allowing sets to be constructed by providing an arbitrary property is too powerful.
Later versions of set theory restrict the formation of sets to remove the paradox.

A related paradox can be constructed in versions of dependent type theory that assign the type `Type` to `Type`.
To ensure that Lean has consistent logical foundations and can be used as a tool for mathematics, `Type` needs to have some other type.
This type is called `Type 1`:
```lean
{{#example_in Examples/Universes.lean TypeType}}
```
```output info
{{#example_out Examples/Universes.lean TypeType}}
```
Similarly, `{{#example_in Examples/Universes.lean Type1Type}}` is a `{{#example_out Examples/Universes.lean Type1Type}}`,
`{{#example_in Examples/Universes.lean Type2Type}}` is a `{{#example_out Examples/Universes.lean Type2Type}}`,
`{{#example_in Examples/Universes.lean Type3Type}}` is a `{{#example_out Examples/Universes.lean Type3Type}}`, and so forth.

Function types occupy the smallest universe that can contain both the argument type and the return type.
This means that `{{#example_in Examples/Universes.lean NatNatType}}` is a `{{#example_out Examples/Universes.lean NatNatType}}`, `{{#example_in Examples/Universes.lean Fun00Type}}` is a `{{#example_out Examples/Universes.lean Fun00Type}}`, and `{{#example_in Examples/Universes.lean Fun12Type}}` is a `{{#example_out Examples/Universes.lean Fun12Type}}`.

## User Defined Types

Structures and inductive datatypes can be declared to inhabit particular universes.
Lean then checks whether each datatype avoids paradoxes by being in a universe that's large enough to prevent it from containing its own type.
For instance, in the following declaration, `MyList` is declared to reside in `Type`, and so is its type argument `α`:
```lean
{{#example_decl Examples/Universes.lean MyList1}}
```
`{{#example_in Examples/Universes.lean MyList1Type}}` itself is a `{{#example_out Examples/Universes.lean MyList1Type}}`.
This means that it cannot be used to contain actual types, because then its argument would be `Type`, which is a `Type 1`:
```lean
{{#example_in Examples/Universes.lean myListNat1Err}}
```
```output error
{{#example_out Examples/Universes.lean myListNat1Err}}
```

Updating `MyList` so that its argument is a `Type 1` results in a definition rejected by Lean:
```lean
{{#example_in Examples/Universes.lean MyList2}}
```
```output error
{{#example_out Examples/Universes.lean MyList2}}
```
This error occurs because the argument to `cons` with type `α` is from a larger universe than `MyList`.
Placing `MyList` itself in `Type 1` solves this issue, but at the cost of `MyList` now being itself inconvenient to use in contexts that expect a `Type`.

The specific rules that govern whether a datatype is allowed are somewhat complicated.
Generally speaking, it's easiest to start with the datatype in the same universe as the largest of its arguments.
Then, if Lean rejects the definition, increase its level by one, which will usually go through.

## Universe Polymorphism

Defining a datatype in a specific universe can lead to code duplication.
Placing `MyList` in `Type → Type` means that it can't be used for an actual list of types.
Placing it in `Type 1 → Type 1` means that it can't be used for a list of lists of types.
Rather than copy-pasting the datatype to create versions in `Type`, `Type 1`, `Type 2`, and so on, a feature called _universe polymorphism_ can be used to write a single definition that can be instantiated in any of these universes.

Ordinary polymorphic types use variables to stand for types in a definition.
This allows Lean to fill in the variables differently, which enables these definitions to be used with a variety of types.
Similarly, universe polymorphism allows variables to stand for universes in a definition, enabling Lean to fill them in differently so that they can be used with a variety of universes.
Just as type arguments are conventionally named with Greek letters, universe arguments are conventionally named `u`, `v`, and `w`.

This definition of `MyList` doesn't specify a particular universe level, but instead uses a variable `u` to stand for any level.
If the resulting datatype is used with `Type`, then `u` is `0`, and if it's used with `Type 3`, then `u` is `3`:
```lean
{{#example_decl Examples/Universes.lean MyList3}}
```

With this definition, the same definition of `MyList` can be used to contain both actual natural numbers and the natural number type itself:
```lean
{{#example_decl Examples/Universes.lean myListOfNat3}}
```
It can even contain itself:
```lean
{{#example_decl Examples/Universes.lean myListOfList3}}
```

It would seem that this would make it possible to write a logical paradox.
After all, the whole point of the universe system is to rule out self-referential types.
Behind the scenes, however, each occurrence of `MyList` is provided with a universe level argument.
In essence, the universe-polymorphic definition of `MyList` created a _copy_ of the datatype at each level, and the level argument selects which copy is to be used.
These level arguments are written with a dot and curly braces, so `{{#example_in Examples/Universes.lean MyListDotZero}} : {{#example_out Examples/Universes.lean MyListDotZero}}`, `{{#example_in Examples/Universes.lean MyListDotOne}} : {{#example_out Examples/Universes.lean MyListDotOne}}`, and `{{#example_in Examples/Universes.lean MyListDotTwo}} : {{#example_out Examples/Universes.lean MyListDotTwo}}`.

Writing the levels explicitly, the prior example becomes:
```lean
{{#example_decl Examples/Universes.lean myListOfList3Expl}}
```

When a universe-polymorphic definition takes multiple types as arguments, it's a good idea to give each argument its own level variable for maximum flexibility.
For example, a version of `Sum` with a single level argument can be written as follows:
```lean
{{#example_decl Examples/Universes.lean SumNoMax}}
```
This definition can be used at multiple levels:
```lean
{{#example_decl Examples/Universes.lean SumPoly}}
```
However, it requires that both arguments be in the same universe:
```lean
{{#example_in Examples/Universes.lean stringOrTypeLevels}}
```
```output error
{{#example_out Examples/Universes.lean stringOrTypeLevels}}
```

This datatype can be made more flexible by using different variables for the two type arguments' universe levels, and then declaring that the resulting datatype is in the largest of the two:
```lean
{{#example_decl Examples/Universes.lean SumMax}}
```
This allows `Sum` to be used with arguments from different universes:
```lean
{{#example_decl Examples/Universes.lean stringOrTypeSum}}
```
    
In positions where Lean expects a universe level, any of the following are allowed:
 * A concrete level, like `0` or `1`
 * A variable that stands for a level, such as `u` or `v`
 * The maximum of two levels, written as `max` applied to the levels
 * A level increase, written with `+ 1`

### Writing Universe-Polymorphic Definitions

Until now, every datatype defined in this book has been in the smallest universe.
When presenting polymorphic datatypes from the Lean standard library, such as `List` and `Sum`, this book created non-polymorphic versions of them.
The real versions use universe polymorphism to enable code re-use between type-level and non-type-level programs.

There are a few general guidelines to follow when writing universe-polymorphic types.
First off, independent type arguments should have different universe variables, which enables the polymorphic definition to be used with a wider variety of arguments, increasing the potential for code reuse.
Secondly, the whole type is itself typically either in the maximum of all the universe variables, or one greater than this maximum.
Try the smaller of the two first.
Finally, it's a good idea to put the new type in as small of a universe as possible, which allows it to be use more flexibly in other contexts.
Non-polymorphic types, such as `Nat` and `String`, can be placed directly in `Type 0`.

### `Prop` and Polymorphism

Just as `Type`, `Type 1`, and so on describe types that classify programs and data, `Prop` classifies logical propositions.
A type in `Prop` describes what counts as convincing evidence for the truth of a statement.
Propositions are like ordinary types in many ways: they can be declared inductively, they can have constructors, and functions can take propositions as arguments.
However, unlike datatypes, it typically doesn't matter _which_ evidence is provided for the truth of a statement, only _that_ evidence is provided.
On the other hand, it is very important that a program not only return a `Nat`, but that it's the _correct_ `Nat`.

`Prop` is at the bottom of the universe hierarchy, and the type of `Prop` is `Type`.
This means that lists of propositions have type `List Type`:
```lean
{{#example_decl Examples/Universes.lean someTrueProps}}
```
Filling out the universe argument explicitly demonstrates that `Prop` is a `Type`:
```lean
{{#example_decl Examples/Universes.lean someTruePropsExp}}
```

Behind the scenes, `Prop` and `Type` are united into a single hierarchy called `Sort`.
`Prop` is the same as `Sort 0`, `Type 0` is `Sort 1`, `Type 1` is `Sort 2`, and so forth.
When writing programs with Lean, this is typically not relevant, but it may occur in error messages from time to time, and it explains the name of the `CoeSort` class.

## Polymorphism in Practice

In the remainder of the book, definitions of polymorphic datatypes, structures, and classes will use universe polymorphism in order to be consistent with the Lean standard library.
This will enable the complete presentation of the `Functor`, `Applicative`, and `Monad` classes to be completely consistent with their actual definitions.
