# Alternatives

`Validate` can also be used in situations where there is more than one way for input to be acceptable.
For the input form `RawInput`, an alternative set of business rules that implement conventions from a legacy system might be the following:

 0. All human users must provide a birth year that is four digits.
 1. Users born prior to 1970 do not need to provide names, due to incomplete older records.
 2. Users born after 1970 must provide names.
 3. Companies should enter `"FIRM"` as their year of birth instead and provide a company name.
 
No particular provision is made for users born in 1970.
It is expected that they will either give up, lie about their year of birth, or call.
The company considers this an acceptable cost of doing business.
 
The following inductive type captures the values that can be produced from these stated rules:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean LegacyCheckedInput}}
```

A validator for these rules is more complicated, however, as it must address all three cases.
While it can be written as a series of nested `if` expressions, it's easier to design the three cases independently and then combine them.
This requires a means of recovering from failure while preserving error messages:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean ValidateorElse}}
```



## Exercises

### Improve Validation Friendliness

The errors returned from `Validate` programs that use `<|>` can be difficult to read, because inclusion in the list of errors simply means that the error can be reached through _some_ code path.
A more structured error report can be used to guide the user through the process more accurately:

 * Replace the `NonEmptyList` in `Validate.error` with a bare type variable, and then update the definitions of the `Applicative (Validate ε)` and `OrElse (Validate ε α)` instances to require only that there be an `Append ε` instance available.
 * Define a function `Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α` that transforms all the errors in a validation run.
 * Using the datatype `TreeError` to represent errors, rewrite the legacy validation system to track its path through the three alternatives.
 * Write a function `report : TreeError → String` that outputs a user-friendly view of the `TreeError`'s accumulated warnings and errors.
 
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean TreeError}}
```


