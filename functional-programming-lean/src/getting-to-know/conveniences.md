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
In many cases, intermediate values represent useful concepts all on their own, and naming them explicitly can make the program easier to read.
In other cases, the intermediate value is used more than once.
As in most other languages, writing down the same code twice in Lean causes it to be computed twice, while saving the result in a variable leads to the result of the computation being saved and re-used.

For instance, `unzip` is a function that transforms a list of pairs into a pair of lists.
When the list of pairs is empty, then the result of `unzip` is a pair of empty lists.
When the list of pairs has a pair at its head, then the two fields of the pair are added to the result of unzipping the rest of the list.
This definition of `unzip` follows that description exactly:
```Lean
{{#example_decl Examples/Intro.lean unzipBad}}
```
Unfortunately, there is a problem: this code is slower than it needs to be.
Each entry in the list of pairs leads to two recursive calls, which makes this function take exponential time.
However, both recursive calls will have the same result, so there is no reason to make the recursive call twice.


In Lean, the result of the recursive call can be named, and thus saved, using `let`.
Local definitions with `let` resemble top-level definitions with `def`: it takes a name to be locally defined, arguments if desired, a type signature, and then a body following `:=`.
A semicolon is used after the local definition.
For instance, `let` can be used in `unzip` like this:
```Lean
{{#example_decl Examples/Intro.lean unzip}}
```
The biggest difference between `let` and `def` is that recursive `let` definitions must be explicitly indicated by writing `let rec`.


# Type Inference

In many situations, Lean can automatically determine an expression's type.
In these cases, explicit types may be omitted from both top-level definitions (with `def`) and local definitions (with `let`).
For instance, the recursive call to `unzip` does not need an annotation:
```Lean
{{#example_decl Examples/Intro.lean unzip}}
```

As a rule of thumb, omitting the types of literal values (like strings and numbers) usually works, although Lean may pick a type for literal numbers that is more specific than the intended type.
Lean can usually determine a type for a function application, because it already knows the argument types and the return type.
Omitting return types for function definitions will often work, but function arguments typically require annotations.
Definitions that are not functions, like `unzipped` in the example, do not need types if their bodies do not need types, and the body of this definition is a function application.

Omitting the return type for `unzip` is possible when using an explicit `match` expression:
```Lean
{{#example_decl Examples/Intro.lean unzipNRT}}
```


Generally speaking, it is a good idea to err on the side of too many, rather than too few, type annotations.
First off, explicit types communicate assumptions about the code to readers.
Even if Lean can determine the type on its own, it can still be easier to read code without having to repeatedly query Lean for type information.
Secondly, explicit types help localize errors.
The more explicit a program is about its types, the more informative the error messages can be.
This is especially important in a language like Lean that has a very expressive type system.
Thirdly, explicit types make it easier to write the program in the first place.
The type is a specification, and the compiler's feedback can be a helpful tool in writing a program that meets the specification.
Finally, Lean's type reconstruction is a best-effort system.
Because Lean's type system is so expressive, there is no "best" or most general type to find for all expressions.
This means that even if you get a type, there's no guarantee that it's the _right_ type for a given application.
For instance, `14` can be a `Nat` or an `Int`:
```Lean
{{#example_in Examples/Intro.lean fourteenNat}}
```
```Lean info
{{#example_out Examples/Intro.lean fourteenNat}}
```
```Lean
{{#example_in Examples/Intro.lean fourteenInt}}
```
```Lean info
{{#example_out Examples/Intro.lean fourteenInt}}
```

Missing type annotations can give confusing error messages.
Omitting all types from the definition of `unzip`:
```Lean
{{#example_in Examples/Intro.lean unzipNoTypesAtAll}}
```
leads to a message about the `match` expression:
```Lean error
{{#example_out Examples/Intro.lean unzipNoTypesAtAll}}
```
This is because `match` needs to know the type of the value being inspected, but that type was not available.
A "metavariable" is an unknown part of a program, written `?m.XYZ` in error messages—they are described in the [section on Polymorphism](getting-to-know/polymorphism.md).
In this program, the type annotation on the argument is required.

Even some very simple programs require type annotations.
For instance, the identity function just returns whatever argument it is passed.
With argument and type annotations, it looks like this:
```Lean
{{#example_decl Examples/Intro.lean idA}}
```
Lean is capable of determining the return type on its own:
```Lean
{{#example_decl Examples/Intro.lean idA}}
```
Omitting the argument type, however, causes an error:
```Lean
{{#example_in Examples/Intro.lean identNoTypes}}
```
```Lean error
{{#example_out Examples/Intro.lean identNoTypes}}
```

In general, messages that say something like "failed to infer" or that mention metavariables are often a sign that more type annotations are necessary.
Especially while still learning Lean, it is useful to write down many types.

# Simultaneous Matching

Pattern-matching expressions, just like pattern-matching definitions, can match on multiple values at once.
Both the expressions to be inspected and the patterns that they match against are written with commas between them, similarly to the syntax used for definitions.
Here is a version of `drop` that uses simultaneous matching:
```Lean
{{#example_decl Examples/Intro.lean dropMatch}}
```

# Lambda

# Namespaces

# Sections and Variables

# if let

# Positional Structure Arguments

# String Interpolation

