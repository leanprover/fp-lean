# Polymorphism

Just as in most languages, types in Lean can take arguments.
For instance, the type `List Nat` describes lists of natural numbers, `List String` describes lists of strings, and `List (List Point)` describes lists of lists of points.
This is very similar to `List<Nat>`, `List<String>`, or `List<List<Point>>` in a language like C# or Java.
Just as Lean uses a space to pass an argument to a function, it uses a space to pass an argument to a type.

In functional programming, the term _polymorphism_ typically refers to datatypes and definitions that take types as arguments.
This is different from the object-oriented programming community, where the term typically refers to subclasses that may override some behavior of their superclass.
In this book, "polymorphism" always refers to the first sense of the word.
These type arguments can be used in the datatype or definition, which allows the same datatype or definition to be used with any type that results from replacing the arguments' names with some other types.

The `Point` structure requires that both the `x` and `y` fields are `Float`s.
There is, however, nothing about points that require a specific representation for each coordinate.
A polymorphic version of `Point`, called `PPoint`, can take a type as an argument, and then use that type for both fields:
```lean
{{#example_decl Examples/Intro.lean PPoint}}
```
Just as a function definition's arguments are written immediately after the name being defined, a structure's arguments are written immediately after the structure's name.
It is customary to use Greek letters to name type arguments in Lean when no more specific name suggests itself.
`Type` is a type that describes other types, so `Nat`, `List String`, and `PPoint Int` all have type `Type`.

Just like `List`, `PPoint` can be used by providing a specific type as its argument:
```lean
{{#example_decl Examples/Intro.lean natPoint}}
```
In this example, both fields are expected to be `Nat`s.
Just as a function is called by replacing its argument variables with its argument values, providing `PPoint` with the type `Nat` as an argument yields a structure in which the fields `x` and `y` have the type `Nat`, because the argument name `α` has been replaced by the argument type `Nat`.
Because types are ordinary expressions in Lean, passing arguments to polymorphic types (like `PPoint`) doesn't require any special syntax.

Definitions may also take types as arguments, which makes them polymorphic.
The function `replaceX` replaces the `x` field of a `PPoint` with a new value.
In order to allow `replaceX` to work with _any_ polymorphic point, it must be polymorphic itself.
This is achieved by having its first argument be the type of the point's fields, with later arguments referring back to the first argument's name.
```lean
{{#example_decl Examples/Intro.lean replaceX}}
```
In other words, when the types of the arguments `point` and `newX` mention `α`, they are referring to _whichever type was provided as the first argument_.
This is similar to the way that function argument names refer to the values that were provided when they occur in the function's body.

This can be seen by asking Lean to check the type of `replaceX`, and then asking it to check the type of `replaceX Nat`.
```lean
{{#example_in Examples/Intro.lean replaceXT}}
```
```output info
{{#example_out Examples/Intro.lean replaceXT}}
```
This function type includes the _name_ of the first argument, and later arguments in the type refer back to this name.
Just as the value of a function application is found by replacing the argument name with the provided argument value in the function's body, the type of a function application is found by replacing the argument's name with the provided value in the function's return type.
Providing the first argument, `Nat`, causes all occurrences of `α` in the remainder of the type to be replaced with `Nat`:
```lean
{{#example_in Examples/Intro.lean replaceXNatT}}
```
```output info
{{#example_out Examples/Intro.lean replaceXNatT}}
```
Because the remaining arguments are not explicitly named, no further substitution occurs as more arguments are provided:
```lean
{{#example_in Examples/Intro.lean replaceXNatOriginT}}
```
```output info
{{#example_out Examples/Intro.lean replaceXNatOriginT}}
```
```lean
{{#example_in Examples/Intro.lean replaceXNatOriginFiveT}}
```
```output info
{{#example_out Examples/Intro.lean replaceXNatOriginFiveT}}
```
The fact that the type of the whole function application expression was determined by passing a type as an argument has no bearing on the ability to evaluate it.
```lean
{{#example_in Examples/Intro.lean replaceXNatOriginFiveV}}
```
```output info
{{#example_out Examples/Intro.lean replaceXNatOriginFiveV}}
```

Polymorphic functions work by taking a named type argument and having later types refer to the argument's name.
However, there's nothing special about type arguments that allows them to be named.
Given a datatype that represents positive or negative signs:
```lean
{{#example_decl Examples/Intro.lean Sign}}
```
it is possible to write a function whose argument is a sign.
If the argument is positive, the function returns a `Nat`, while if it's negative, it returns an `Int`:
```lean
{{#example_decl Examples/Intro.lean posOrNegThree}}
```
Because types are first class and can be computed using the ordinary rules of the Lean language, they can be computed by pattern-matching against a datatype.
When Lean is checking this function, it uses the fact that the function's body pattern-matches to run the same pattern in the type, showing that `Nat` is the expected type for the `pos` case and that `Int` is the expected type for the `neg` case.

## Linked Lists

Lean's standard library includes a canonical linked list datatype, called `List`, and special syntax that makes it more convenient to use.
Lists are written in square brackets.
For instance, a list that contains the prime numbers less than 10 can be written:
```lean
{{#example_decl Examples/Intro.lean primesUnder10}}
```

Behind the scenes, `List` is an inductive datatype, defined like this:
```lean
{{#example_decl Examples/Intro.lean List}}
```
The actual definition in the standard library is slightly different, because it uses features that have not yet been presented, but it is substantially similar.
This definition says that `List` takes a single type as its argument, just as `PPoint` did.
This type is the type of the entries stored in the list.
According to the constructors, a `List α` can be built with either `nil` or `cons`.
The constructor `nil` represents empty lists, and the constructor `cons` represents a single element in the linked list.
The first argument to `cons` is the head of the list, and the second argument is its tail.

The `primesUnder10` example can be written more explicitly by using `List`'s constructors directly:
```lean
{{#example_decl Examples/Intro.lean explicitPrimesUnder10}}
```
These two definitions are completely equivalent, but `primesUnder10` is much easier to read than `explicitPrimesUnder10`.

Functions that consume `List`s can be defined in much the same way as functions that consume `Nat`s.
Indeed, one way to think of a linked list is as a `Nat` that has an extra data field dangling off each `succ` constructor.
From this point of view, computing the length of a list is the process of replacing each `cons` with a `succ` and the final `nil` with a `zero`.
Just as `replaceX` took the type of the fields of the point as an argument, `length` takes the type of the list's entries.
For example, if the list contains strings, then the first argument is `String`: `{{#example_eval Examples/Intro.lean length1EvalSummary 0}}`.
It should compute like this:
```
{{#example_eval Examples/Intro.lean length1EvalSummary}}
```

The definition of `length` is both polymorphic (because it takes the list entry type as an argument) and recursive (because it refers to itself).
Generally, functions follow the shape of the data: recursive datatypes lead to recursive functions, and polymorphic datatypes lead to polymorphic functions.
```lean
{{#example_decl Examples/Intro.lean length1}}
```

Names such as `xs` and `ys` are conventionally used to stand for lists of unknown values.
The `s` in the name indicates that they are plural, so they are pronounced "exes" and "whys" rather than "x s" and "y s".

To make it easier to read functions on lists, the bracket notation `[]` can be used to pattern-match against `nil`, and an infix `::` can be used in place of `cons`:
```lean
{{#example_decl Examples/Intro.lean length2}}
```

## Implicit Arguments

Both `replaceX` and `length` are somewhat bureaucratic to use, because the type argument is typically uniquely determined by the later values.
Indeed, in most languages, the compiler is perfectly capable of determining type arguments on its own, and only occasionally needs help from users.
This is also the case in Lean.
Arguments can be declared _implicit_ by wrapping them in curly braces instead of parentheses when defining a function.
For instance, a version of `replaceX` with an implicit type argument looks like this:
```lean
{{#example_decl Examples/Intro.lean replaceXImp}}
```
It can be used with `natOrigin` without providing `Nat` explicitly, because Lean can _infer_ the value of `α` from the later arguments:
```lean
{{#example_in Examples/Intro.lean replaceXImpNat}}
```
```output info
{{#example_out Examples/Intro.lean replaceXImpNat}}
```

Similarly, `length` can be redefined to take the entry type implicitly:
```lean
{{#example_decl Examples/Intro.lean lengthImp}}
```
This `length` function can be applied directly to `primesUnder10`:
```lean
{{#example_in Examples/Intro.lean lengthImpPrimes}}
```
```output info
{{#example_out Examples/Intro.lean lengthImpPrimes}}
```

In the standard library, Lean calls this function `List.length`, which means that the dot syntax that is used for structure field access can also be used to find the length of a list:
```lean
{{#example_in Examples/Intro.lean lengthDotPrimes}}
```
```output info
{{#example_out Examples/Intro.lean lengthDotPrimes}}
```


Just as C# and Java require type arguments to be provided explicitly from time to time, Lean is not always capable of finding implicit arguments.
In these cases, they can be provided using their names.
For instance, a version of `List.length` that only works for lists of integers can be specified by setting `α` to `Int`:
```lean
{{#example_in Examples/Intro.lean lengthExpNat}}
```
```output info
{{#example_out Examples/Intro.lean lengthExpNat}}
```

## More Built-In Datatypes

In addition to lists, Lean's standard library contains a number of other structures and inductive datatypes that can be used in a variety of contexts.

### `Option`
Not every list has a first entry—some lists are empty.
Many operations on collections may fail to find what they are looking for.
For instance, a function that finds the first entry in a list may not find any such entry.
It must therefore have a way to signal that there was no first entry.

Many languages have a `null` value that represents the absence of a value.
Instead of equipping existing types with a special `null` value, Lean provides a datatype called `Option` that equips some other type with an indicator for missing values.
For instance, a nullable `Int` is represented by `Option Int`, and a nullable list of strings is represented by the type `Option (List String)`.
Introducing a new type to represent nullability means that the type system ensures that checks for `null` cannot be forgotten, because an `Option Int` can't be used in a context where an `Int` is expected.

`Option` has two constructors, called `some` and `none`, that respectively represent the non-null and null versions of the underlying type.
The non-null constructor, `some`, contains the underlying value, while `none` takes no arguments:
```lean
{{#example_decl Examples/Intro.lean Option}}
```

The `Option` type is very similar to nullable types in languages like C# and Kotlin, but it is not identical.
In these languages, if a type (say, `Boolean`) always refers to actual values of the type (`true` and `false`), the type `Boolean?` or `Nullable<Boolean>` additionally admits the `null` value.
Tracking this in the type system is very useful: the type checker and other tooling can help programmers remember to check for null, and APIs that explicitly describe nullability through type signatures are more informative than ones that don't.
However, these nullable types differ from Lean's `Option` in one very important way, which is that they don't allow multiple layers of optionality.
`{{#example_out Examples/Intro.lean nullThree}}` can be constructed with `{{#example_in Examples/Intro.lean nullOne}}`, `{{#example_in Examples/Intro.lean nullTwo}}`, or `{{#example_in Examples/Intro.lean nullThree}}`.
C#, on the other hand, forbids multiple layers of nullability by only allowing `?` to be added to non-nullable types, while Kotlin treats `T??` as being equivalent to `T?`.
This subtle difference is rarely relevant in practice, but it can matter from time to time.

To find the first entry in a list, if it exists, use `List.head?`.
The question mark is part of the name, and is not related to the use of question marks to indicate nullable types in C# or Kotlin.
In the definition of `List.head?`, an underscore is used to represent the tail of the list.
In patterns, underscores match anything at all, but do not introduce variables to refer to the matched data.
Using underscores instead of names is a way to clearly communicate to readers that part of the input is ignored.
```lean
{{#example_decl Examples/Intro.lean headHuh}}
```
A Lean naming convention is to define operations that might fail in groups using the suffixes `?` for a version that returns an `Option`, `!` for a version that crashes when provided with invalid input, and `D` for a version that returns a default value when the operation would otherwise fail.
For instance, `head` requires the caller to provide mathematical evidence that the list is not empty, `head?` returns an `Option`, `head!` crashes the program when passed an empty list, and `headD` takes a default value to return in case the list is empty.
The question mark and exclamation mark are part of the name, not special syntax, as Lean's naming rules are more liberal than many languages.

Because `head?` is defined in the `List` namespace, it can be used with accessor notation:
```lean
{{#example_in Examples/Intro.lean headSome}}
```
```output info
{{#example_out Examples/Intro.lean headSome}}
```
However, attempting to test it on the empty list leads to two errors:
```lean
{{#example_in Examples/Intro.lean headNoneBad}}
```
```output error
{{#example_out Examples/Intro.lean headNoneBad}}

{{#example_out Examples/Intro.lean headNoneBad2}}
```
This is because Lean was unable to fully determine the expression's type.
In particular, it could neither find the implicit type argument to `List.head?`, nor could it find the implicit type argument to `List.nil`.
In Lean's output, `?m.XYZ` represents a part of a program that could not be inferred.
These unknown parts are called _metavariables_, and they occur in some error messages.
In order to evaluate an expression, Lean needs to be able to find its type, and the type was unavailable because the empty list does not have any entries from which the type can be found.
Explicitly providing a type allows Lean to proceed:
```lean
{{#example_in Examples/Intro.lean headNone}}
```
```output info
{{#example_out Examples/Intro.lean headNone}}
```
The error messages provide a useful clue.
Both messages use the _same_ metavariable to describe the missing implicit argument, which means that Lean has determined that the two missing pieces will share a solution, even though it was unable to determine the actual value of the solution.

### `Prod`

The `Prod` structure, short for "Product", is a generic way of joining two values together.
For instance, a `Prod Nat String` contains a `Nat` and a `String`.
In other words, `PPoint Nat` could be replaced by `Prod Nat Nat`.
`Prod` is very much like C#'s tuples, the `Pair` and `Triple` types in Kotlin, and `tuple` in C++.
Many applications are best served by defining their own structures, even for simple cases like `Point`, because using domain terminology can make it easier to read the code.

On the other hand, there are some cases where it is not worth the overhead of defining a new type.
Additionally, some libraries are sufficiently generic that there is no more specific concept than "pair".
Finally, the standard library contains a variety of convenience functions that make it easier to work with the built-in pair type.

The standard pair structure is called `Prod`.
```lean
{{#example_decl Examples/Intro.lean Prod}}
```
Lists are used so frequently that there is special syntax to make them more readable.
For the same reason, both the product type and its constructor have special syntax.
The type `Prod α β` is typically written `α × β`, mirroring the usual notation for a Cartesian product of sets.
Similarly, the usual mathematical notation for pairs is available for `Prod`.
In other words, instead of writing:
```lean
{{#example_decl Examples/Intro.lean fivesStruct}}
```
it suffices to write:
```lean
{{#example_decl Examples/Intro.lean fives}}
```

Both notations are right-associative.
This means that the following definitions are equivalent:
```lean
{{#example_decl Examples/Intro.lean sevens}}

{{#example_decl Examples/Intro.lean sevensNested}}
```
In other words, all products of more than two types, and their corresponding constructors, are actually nested products and nested pairs behind the scenes.



### `Sum`

The `Sum` datatype is a generic way of allowing a choice between values of two different types.
For instance, a `Sum String Int` is either a `String` or an `Int`.
Like `Prod`, `Sum` should be used either when writing very generic code, for a very small section of code where there is no sensible domain-specific type, or when the standard library contains useful functions.
In most situations, it is more readable and maintainable to use a custom inductive type.

Values of type `Sum α β` are either the constructor `inl` applied to a value of type `α` or the constructor `inr` applied to a value of type `β`:
```lean
{{#example_decl Examples/Intro.lean Sum}}
```
These names are abbreviations for "left injection" and "right injection", respectively.
Just as the Cartesian product notation is used for `Prod`, a "circled plus" notation is used for `Sum`, so `α ⊕ β` is another way to write `Sum α β`.
There is no special syntax for `Sum.inl` and `Sum.inr`.

For instance, if pet names can either be dog names or cat names, then a type for them can be introduced as a sum of strings:
```lean
{{#example_decl Examples/Intro.lean PetName}}
```
In a real program, it would usually be better to define a custom inductive datatype for this purpose with informative constructor names.
Here, `Sum.inl` is to be used for dog names, and `Sum.inr` is to be used for cat names.
These constructors can be used to write a list of animal names:
```lean
{{#example_decl Examples/Intro.lean animals}}
```
Pattern matching can be used to distinguish between the two constructors.
For instance, a function that counts the number of dogs in a list of animal names (that is, the number of `Sum.inl` constructors) looks like this:
```lean
{{#example_decl Examples/Intro.lean howManyDogs}}
```
Function calls are evaluated before infix operators, so `howManyDogs morePets + 1` is the same as `(howManyDogs morePets) + 1`.
As expected, `{{#example_in Examples/Intro.lean dogCount}}` yields `{{#example_out Examples/Intro.lean dogCount}}`.

### `Unit`

`Unit` is a type with just one argumentless constructor, called `unit`.
In other words, it describes only a single value, which consists of said constructor applied to no arguments whatsoever.
`Unit` is defined as follows:
```lean
{{#example_decl Examples/Intro.lean Unit}}
```

On its own, `Unit` is not particularly useful.
However, in polymorphic code, it can be used as a placeholder for data that is missing.
For instance, the following inductive datatype represents arithmetic expressions:
```lean
{{#example_decl Examples/Intro.lean ArithExpr}}
```
The type argument `ann` stands for annotations, and each constructor is annotated.
Expressions coming from a parser might be annotated with source locations, so a return type of `ArithExpr SourcePos` ensures that the parser put a `SourcePos` at each subexpression.
Expressions that don't come from the parser, however, will not have source locations, so their type can be `ArithExpr Unit`.


Additionally, because all Lean functions have arguments, zero-argument functions in other languages can be represented as functions that take a `Unit` argument.
In a return position, the `Unit` type is similar to `void` in languages derived from C.
In the C family, a function that returns `void` will return control to its caller, but it will not return any interesting value.
By being an intentionally uninteresting value, `Unit` allows this to be expressed without requiring a special-purpose `void` feature in the type system.
Unit's constructor can be written as empty parentheses: `{{#example_in Examples/Intro.lean unitParens}} : {{#example_out Examples/Intro.lean unitParens}}`.

### `Empty`

The `Empty` datatype has no constructors whatsoever.
Thus, it indicates unreachable code, because no series of calls can ever terminate with a value at type `Empty`.

`Empty` is not used nearly as often as `Unit`.
However, it is useful in some specialized contexts.
Many polymorphic datatypes do not use all of their type arguments in all of their constructors.
For instance, `Sum.inl` and `Sum.inr` each use only one of `Sum`'s type arguments.
Using `Empty` as one of the type arguments to `Sum` can rule out one of the constructors at a particular point in a program.
This can allow generic code to be used in contexts that have additional restrictions.

### Naming: Sums, Products, and Units

Generally speaking, types that offer multiple constructors are called _sum types_, while types whose single constructor takes multiple arguments are called _product types_.
These terms are related to sums and products used in ordinary arithmetic.
The relationship is easiest to see when the types involved contain a finite number of values.
If `α` and `β` are types that contain _n_ and _k_ distinct values, respectively, then `α ⊕ β` contains _n_ + _k_ distinct values and `α × β` contains _n_ × _k_ distinct values.
For instance, `Bool` has two values: `true` and `false`, and `Unit` has one value: `Unit.unit`.
The product `Bool × Unit` has the two values `(true, Unit.unit)` and `(false, Unit.unit)`, and the sum `Bool ⊕ Unit` has the three values `Sum.inl true`, `Sum.inl false`, and `Sum.inr unit`.
Similarly, 2 × 1 = 2, and 2 + 1 = 3.

## Messages You May Meet

Not all definable structures or inductive types can have the type `Type`.
In particular, if a constructor takes an arbitrary type as an argument, then the inductive type must have a different type.
These errors usually state something about "universe levels".
For example, for this inductive type:
```lean
{{#example_in Examples/Intro.lean TypeInType}}
```
Lean gives the following error:
```output error
{{#example_out Examples/Intro.lean TypeInType}}
```
A later chapter describes why this is the case, and how to modify definitions to make them work.
For now, try making the type an argument to the inductive type as a whole, rather than to the constructor.

Similarly, if a constructor's argument is a function that takes the datatype being defined as an argument, then the definition is rejected.
For example:
```lean
{{#example_in Examples/Intro.lean Positivity}}
```
yields the message:
```output error
{{#example_out Examples/Intro.lean Positivity}}
```
For technical reasons, allowing these datatypes could make it possible to undermine Lean's internal logic, making it unsuitable for use as a theorem prover.

Forgetting an argument to an inductive type can also yield a confusing message.
For example, when the argument `α` is not passed to `MyType` in `ctor`'s type:
```lean
{{#example_in Examples/Intro.lean MissingTypeArg}}
```
Lean replies with the following error:
```output error
{{#example_out Examples/Intro.lean MissingTypeArg}}
```
The error message is saying that `MyType`'s type, which is `Type → Type`, does not itself describe types.
`MyType` requires an argument to become an actual honest-to-goodness type.

The same message can appear when type arguments are omitted in other contexts, such as in a type signature for a definition:
```lean
{{#example_decl Examples/Intro.lean MyTypeDef}}

{{#example_in Examples/Intro.lean MissingTypeArg2}}
```

## Exercises

 * Write a function to find the last entry in a list. It should return an `Option`.
 * Write a function that finds the first entry in a list that satisfies a given predicate. Start the definition with `def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=`
 * Write a function `Prod.swap` that swaps the two fields in a pair. Start the definition with `def Prod.swap {α β : Type} (pair : α × β) : β × α :=`
 * Rewrite the `PetName` example to use a custom datatype and compare it to the version that uses `Sum`.
 * Write a function `zip` that combines two lists into a list of pairs. The resulting list should be as long as the shortest input list. Start the definition with `def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=`.
 * Write a polymorphic function `take` that returns the first _n_ entries in a list, where _n_ is a `Nat`. If the list contains fewer than `n` entries, then the resulting list should be the input list. `{{#example_in Examples/Intro.lean takeThree}}` should yield `{{#example_out Examples/Intro.lean takeThree}}`, and `{{#example_in Examples/Intro.lean takeOne}}` should yield `{{#example_out Examples/Intro.lean takeOne}}`.
 * Using the analogy between types and arithmetic, write a function that distributes products over sums. In other words, it should have type `α × (β ⊕ γ) → (α × β) ⊕ (α × γ)`.
 * Using the analogy between types and arithmetic, write a function that turns multiplication by two into a sum. In other words, it should have type `Bool × α → α ⊕ α`.
