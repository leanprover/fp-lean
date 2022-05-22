Intro here

# Automatic Implicit Arguments

When writing polymorphic functions in Lean, it is typically not necessary to list all the implicit arguments.
Instead, they can simply be mentioned.
If Lean can determine their type, then they are automatically inserted as implicit arguments.
In other words, the previous definition of `length`:
```Lean
{{#example_decl Examples/Intro.lean lengthImp}}
```
can be written without `{α : Type}`:
```Lean
{{#example_decl Examples/Intro.lean lengthImpAuto}}
```
This can greatly simplify highly polymorphic definitions that take many implicit arguments.

# Pattern-Matching Definitions

When defining functions with `def`, it is quite common to name an argument and then immediately use it with pattern matching.
For instance, in `length`, the argument `xs` is used only in `match`.
In these situations, the cases of the `match` expression can be written directly, without naming the argument at all.

The first step is to move the arguments' types to the right of the definition's type, in the form of a function type.
For instance, the type of `length` is `List α → Nat`.
Then, replace the `:=` with each case of the pattern match:
```Lean
{{#example_decl Examples/Intro.lean lengthMatchDef}}
```

This syntax can also be used to define functions that take more than one argument.
In this case, their patterns are separated by commas.
For instance, `drop` takes a number _n_ and a list, and returns the list after removing the first _n_ entries.
```Lean
{{#example_decl Examples/Intro.lean drop}}
```

Named arguments and patterns can also be used in the same definition.
For instance, a function that takes a default value and an optional value, and returns the default when the optional value is `none`, can be written:
```Lean
{{#example_decl Examples/Intro.lean fromOption}}
```
This function is called `Option.getD` in the standard library, and can be called with dot notation:
```Lean
{{#example_in Examples/Intro.lean getD}}
```
```Lean info
{{#example_out Examples/Intro.lean getD}}
```
```Lean
{{#example_in Examples/Intro.lean getDNone}}
```
```Lean info
{{#example_out Examples/Intro.lean getDNone}}
```

# Local Definitions

It is often useful to name intermediate steps in a computation.
In Lean, this is done using `let`.

```Lean
{{#example_decl Examples/Intro.lean unzip}}
```


# Type Inference



# Multiple Match Targets

# Lambda

# Namespaces

# if let

# Positional Structure Arguments

# String Interpolation

