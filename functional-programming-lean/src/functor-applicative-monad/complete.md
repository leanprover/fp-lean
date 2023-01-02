# The Complete Definitions

The complete definition of the `Functor` class makes use of universe polymorphism and a default method implementation:
```lean
{{#example_decl Examples/FunctorApplicativeMonad/ActualDefs.lean HonestFunctor}}
```
In this definition, `Function.comp` is function composition, which is typically written with the `∘` operator.
`Function.const` is the _constant function_, with type 
