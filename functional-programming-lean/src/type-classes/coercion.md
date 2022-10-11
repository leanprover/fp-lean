# Coercions

In mathematics, it is common to use the same symbol to stand for different aspects of some object in different contexts.
For example, if a ring is referred to in a context where a set is expected, then it is understood that the ring's underlying set is what's intended.
In programming languages, it is common to have rules to automatically translate values of one type into values of another type.
For instance, Java allows a `byte` to be automatically promoted to an `int`, and Kotlin allows a non-nullable type to be used in a context that expects a nullable version of the type.

In Lean, both purposes are served by a mechanism called _coercions_.
When Lean encounters an expression of one type in a context that expects a different type, it will attempt to coerce the expression before reporting a type error.
Unlike Java, C, and Kotlin, the coercions are extensible by defining instances of type classes.

## Positive Numbers

For example, every positive number corresponds to a natural number.
The function `Pos.toNat` converts a `Pos` to the corresponding `Nat`:
```lean
{{#example_decl Examples/Classes.lean posToNat}}
```
The function `List.drop`, with type `{{#example_out Examples/Classes.lean drop}}`, removes a prefix of a list.
Applying `List.drop` to a `Pos`, however, leads to a type error:
```lean
{{#example_in Examples/Classes.lean dropPos}}
```
```output error
{{#example_out Examples/Classes.lean dropPos}}
```

The type class `Coe` describes overloaded ways of coercing from one type to another:
```lean
{{#example_decl Examples/Classes.lean Coe}}
```
An instance of `Coe Pos Nat` is enough to allow the prior code to work:
```lean
{{#example_decl Examples/Classes.lean CoePosNat}}

{{#example_in Examples/Classes.lean dropPosCoe}}
```
```output info
{{#example_out Examples/Classes.lean dropPosCoe}}
```
Using `#check` shows the translation that was used behind the scenes:
```lean
{{#example_in Examples/Classes.lean checkDropPosCoe}}
```
```output info
{{#example_out Examples/Classes.lean checkDropPosCoe}}
```

## Manual Coercion

## Coercing to Types

 - Coe
 - CoeSort
