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
This means that it cannot be used to contain actual types:
```lean
{{#example_in Examples/Universes.lean myListNat1Err}}
```
```output error
{{#example_out Examples/Universes.lean myListNat1Err}}
```

```lean
{{#example_in Examples/Universes.lean MyList2}}
```
```output error
{{#example_out Examples/Universes.lean MyList2}}
```

## Universe Polymorphism

```lean
{{#example_decl Examples/Universes.lean MyList3}}
```

```lean
{{#example_decl Examples/Universes.lean myListOfList3}}
```

```lean
{{#example_decl Examples/Universes.lean myListOfList3Expl}}
```


General rules:
1. Independent type arguments should be in different universes
2. The whole datatype is typically in max or max + 1
3. Keep the whole thing as small as possible - parameters don't bump the level

