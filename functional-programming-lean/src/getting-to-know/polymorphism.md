# Polymorphism

Just as in most languages, types in Lean can take arguments.
For instance, the type `List Nat` describes lists of natural numbers, `List String` describes lists of strings, and `List (List Point)` describes lists of lists of points.
This is very similar to `List<Nat>`, `List<String>`, or `List<List<Point>>` in a language like C# or Java.
Just as Lean uses a space to pass an argument to a function, it uses a space to pass an argument to a type.

In functional programming, the term _polymorphism_ typically refers to datatypes and definitions that can be instantiated at multiple types.
This is different from the object-oriented programming community, where the term typically refers to subclasses that may override some behavior of their superclass.
In this book, "polymorphism" always refers to the first sense of the word.

The `Point` structure requires that both the `x` and `y` fields are `Float`s.
There is, however, nothing about points that require a specific representation for each coordinate.
A polymorphic version of `Point`, called `PPoint`, can take a type as an argument, and then use that type for both fields:
```Lean
{{#example_decl Examples/Intro.lean PPoint}}
```
Just as a function definition's arguments are written immediately after the name being defined, a structure's arguments are written immediately after the structure's name.
It is customary to use Greek letters to name type arguments in Lean when no more specific name suggests itself.
`Type` is a type that describes other types, so `Nat`, `List String`, and `PPoint Int` all have type `Type`.

Just like `List`, `PPoint` can be used by providing a specific type as its argument:
```Lean
{{#example_decl Examples/Intro.lean natPoint}}
```
In this example, both fields are expected to be `Nat`s.
Just as a function is called by replacing its argument variables with its argument values, providing `PPoint` with the type `Nat` as an argument yields a structure in which the fields `x` and `y` should have the type `Nat`, because the argument name `α` has been replaced by the argument type `Nat`.

Definitions may also take types as arguments, which makes them polymorphic.
While some languages have separate notations for type arguments and other arguments, Lean uses a single uniform notation for all arguments.
The function `replaceX` replaces the `x` field of a `PPoint` with a new value.
In order to allow `replaceX` to work with _any_ polymorphic point, it must be polymorphic itself.
This is achieved by having its first argument be the type of the point's fields, and later arguments refer back to the first argument's name.
```Lean
{{#example_decl Examples/Intro.lean replaceX}}
```
In other words, when the types of the arguments `point` and `newX` mention `α`, they are referring to _whichever type was provided as the first argument_.
This is similar to the way that function argument names refer to the values that were provided when they occur in the function's body.

This can be seen by asking Lean to check the type of `replaceX`, and then asking it to check the type of `replaceX Nat`.
```Lean
{{#example_in Examples/Intro.lean replaceXT}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXT}}
```
This function type includes the _name_ of the first argument, and later arguments in the type refer back to this name.
Just as the value of a function application is found by replacing the argument name with the provided argument value in the function's body, the type of a function application is found by replacing the argument's name with the provided value in the function's return type.
Providing the first argument, `Nat`, causes all occurrences of `α` in the remainder of the type to be replaced with `Nat`:
```Lean
{{#example_in Examples/Intro.lean replaceXNatT}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXNatT}}
```
Because the remaining arguments are not explicitly named, no further substitution occurs as more arguments are provided:
```Lean
{{#example_in Examples/Intro.lean replaceXNatOriginT}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXNatOriginT}}
```
```Lean
{{#example_in Examples/Intro.lean replaceXNatOriginFiveT}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXNatOriginFiveT}}
```
The fact that the type of the whole function application expression was determined by passing a type as an argument has no bearing on the ability to evaluate it.
```Lean
{{#example_in Examples/Intro.lean replaceXNatOriginFiveV}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXNatOriginFiveV}}
```

## Linked Lists

Lean's standard library includes a canonical linked list datatype, called `List`, and special syntax that makes it more convenient to use.
Lists are written in square brackets.
For instance, a list that contains the prime numbers less than 10 can be written:
```Lean
{{#example_decl Examples/Intro.lean primesUnder10}}
```

Behind the scenes, `List` is an inductive datatype, defined like this:
```Lean
{{#example_decl Examples/Intro.lean List}}
```
The actual definition in the standard library is slightly different, because it uses features that have not yet been presented, but it is substantially similar.
This definition says that `List` takes a single type as its argument, just as `PPoint` did.
This type is the type of the entries stored in the list.
According to the constructors, a `List α` can be built with either `nil` or `cons`.
The constructor `nil` represents empty lists, and the constructor `cons` represents a single element in the linked list.
The first argument to `cons` is the head of the list, and the second argument is its tail.

The `primesUnder10` example can be written more explicitly by using `List`'s constructors directly:
```Lean
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
```Lean
{{#example_decl Examples/Intro.lean length1}}
```

Names such as `xs` and `ys` are conventionally used to stand for lists of unknown values.
The `s` in the name indicates that they are plural, so they are pronounced "exes" and "whys" rather than "x s" and "y s".

To make it easier to read functions on lists, the bracket notation `[]` can be used to pattern-match against `nil`, and an infix `::` can be used in place of `cons`:
```Lean
{{#example_decl Examples/Intro.lean length2}}
```

## Implicit Arguments

Both `replaceX` and `length` are somewhat bureaucratic to use, because the type argument is typically uniquely determined by the later values.
Indeed, in most languages, the compiler is perfectly capable of determining type arguments on its own, and only occaisionally needs help from users.
This is also the case in Lean.
Arguments can be declared _implicit_ by wrapping them in curly braces instead of parentheses when defining a function.
For instance, a version of `replaceX` with an implicit type argument looks like this:
```Lean
{{#example_decl Examples/Intro.lean replaceXImp}}
```
It can be used with `natOrigin` without providing `Nat` explicitly, because Lean can _infer_ the value of `α` from the later arguments:
```Lean
{{#example_in Examples/Intro.lean replaceXImpNat}}
```
```Lean info
{{#example_out Examples/Intro.lean replaceXImpNat}}
```

Similarly, `length` can be redefined to take the entry type implicitly:
```Lean
{{#example_decl Examples/Intro.lean lengthImp}}
```
This `length` function can be applied directly to `primesUnder10`:
```Lean
{{#example_in Examples/Intro.lean lengthImpPrimes}}
```
```Lean info
{{#example_out Examples/Intro.lean lengthImpPrimes}}
```

In the standard library, Lean calls this function `List.length`, which means that the dot syntax that is used for structure field access can also be used to find the length of a list:
```Lean
{{#example_in Examples/Intro.lean lengthDotPrimes}}
```
```Lean info
{{#example_out Examples/Intro.lean lengthDotPrimes}}
```


Just as C# and Java require type arguments to provided explicitly from time to time, Lean is not always capable of finding implicit arguments.
In these cases, they can be provided using their names.
For instance, a version of `List.length` that only works for lists of integers can be specified by setting `α` to `Int`:
```Lean
{{#example_in Examples/Intro.lean lengthExpNat}}
```
```Lean info
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
```Lean
{{#example_decl Examples/Intro.lean Option}}
```

To find the first entry in a list, if it exists, use `List.head?`.
The question mark is part of the name.
In the definition of `List.head?`, an underscore is used to represent the tail of the list.
In patterns, underscores match anything at all, but do not introduce variables to refer to the matched data.
Using underscores instead of names is a way to clearly communicate to readers that part of the input is ignored.
```Lean
{{#example_decl Examples/Intro.lean headHuh}}
```
A Lean convention is to define operations that might fail in groups.
For instance, `head` requires the caller to provide mathematical evidence that the list is not empty, `head?` returns an `Option`, `head!` crashes the program when passed an empty list, and `headD` takes a default value to return when the operation would otherwise fail.

Because `head?` is defined in the `List` namespace, it can be used with accessor notation:
```Lean
{{#example_in Examples/Intro.lean headSome}}
```
```Lean info
{{#example_out Examples/Intro.lean headSome}}
```
However, attempting to test it on the empty list leads to an error:
```Lean
{{#example_in Examples/Intro.lean headNoneBad}}
```
```Lean error
{{#example_out Examples/Intro.lean headNoneBad}}
```
This is because Lean was unable to fully determine the expression's type.
In Lean's output, `?m.XYZ` represents a part of a program that could not be inferred.
These unknown parts are called _metavariables_ in some error messages.
In this case, Lean cannot find the code to convert an `Option` to a display string because the type inside the option is unknown.
The type was unavailable because the empty list does not have any entries from which the type can be found.
Explicitly providing a type allows Lean to proceed:
```Lean
{{#example_in Examples/Intro.lean headNone}}
```
```Lean info
{{#example_out Examples/Intro.lean headNone}}
```

### `Prod`

The `Prod` structure is a generic way of joining two values together.
For instance, a `Prod Nat String` contains a `Nat` and a `String`.
In other words, `PPoint Nat` could be replaced by `Prod Nat Nat`.
Many applications are best served by defining their own structures, even for simple cases like `Point`, because using domain terminology can make it easier to read the code.

On the other hand, there are some cases where it is not worth the overhead of defining a new type.
Additionally, some libraries are sufficiently generic that there is no more specific concept than "pair".
Finally, the standard library contains a variety of convenience functions that make it easier to work with the built-in pair type.

The standard pair structure is called `Prod`.
```Lean
{{#example_decl Examples/Intro.lean Prod}}
```
However, just as list values are typically built using square brackets and the double-colon operator, there is special syntax for the `Prod` type.
In particular, `Prod α β` is typically written `α × β`, mirroring the usual notation for a Cartesian product of sets.
Similarly, instead of requiring explicit structure notation, the usual mathematical notation for pairs is available for `Prod`.
In other words, instead of writing:
```Lean
{{#example_decl Examples/Intro.lean fivesStruct}}
```
it suffices to write:
```Lean
{{#example_decl Examples/Intro.lean fives}}
```
Both notations are right-associative.
This means that the following definitions are equivalent:
```Lean
{{#example_decl Examples/Intro.lean sevens}}

{{#example_decl Examples/Intro.lean sevensNested}}
```

### `Sum`

The `Sum` datatype is a generic way of allowing a choice between values of two different types.
For instance, a `Sum String Int` is either a `String` or an `Int`.
Like `Prod`, `Sum` should be used either when writing very generic code, for a very small section of code where there is no sensible domain-specific type, or when the standard library contains useful functions.

Values of type `Sum α β` are either the constructor `inl` applied to a value of type `α` or the constructor `inr` applied to a value of type `β`:
```Lean
{{#example_decl Examples/Intro.lean Sum}}
```
These names are abbreviations for "left injection" and "right injection", respectively.
Just as the Cartesian product notation is used for `Prod`, a "circled plus" notation is used for `Sum`, so `α ⊕ β` is another way to write `Sum α β`.

### `Unit`

`Unit` is a type with just one argumentless constructor, called `unit`.
In other words, it describes only a single value, which consists of said constructor applied to no arguments.
On its own, `Unit` is not particularly useful.
However, in polymorphic code, it can be used as a placeholder for data that will be inserted in a later stage of a program.
For instance, a `List Unit` does not contain anything interesting, but it can express how many entries are expected, and they can be inserted later.
Additionally, a function that takes `Unit` as an argument is a way to express a block of code that can be executed on-demand.

The `Unit` type is similar to `void` in languages derived from C.
In the C family, a function that returns `void` will return control to its caller, but it will not return any interesting value.
By being an intentionally uninteresting value, `Unit` allows this to be expressed without requiring a special-purpose `void` feature in the type system.

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
```Lean
{{#example_in Examples/Intro.lean TypeInType}}
```
Lean gives the following error:
```Lean error
{{#example_out Examples/Intro.lean TypeInType}}
```
A later chapter describes why this is the case, and how to modify definitions to make them work.
For now, try making the type an argument to the inductive type as a whole, rather than to the constructor.

Similarly, if a constructor's argument is a function that takes the datatype being defined as an argument, then the definition is rejected.
For example:
```Lean
{{#example_in Examples/Intro.lean Positivity}}
```
yields the message:
```Lean error
{{#example_out Examples/Intro.lean Positivity}}
```
For technical reasons, allowing these datatypes could make it possible to undermine Lean's use as a logic.

## Exercises

 * Write a function to find the last entry in a list. It should return an `Option`.
 * Write a function that finds the first entry in a list that satisfies a given predicate. Start the definition with `def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=`
 * Write a function `Prod.swap` that swaps the two fields in a pair. Start the definition with `def Prod.swap {α β : Type} (pair : α × β) : β × α :=` 
 * Write a function `zip` that combines two lists into a list of pairs. The resulting list should be as long as the shortest input list. Start the definition with `def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=`.
 * Write a polymorphic function `take` that returns the first _n_ entries in a list, where _n_ is a `Nat`. If the list contains fewer than `n` entries, then the resulting list should be the input list. `{{#example_in Examples/Intro.lean takeThree}}` should yield `{{#example_out Examples/Intro.lean takeThree}}`, and `{{#example_in Examples/Intro.lean takeOne}}` should yield `{{#example_out Examples/Intro.lean takeOne}}`.
 * Write a function that distributes products over sums. In other words, it should have type `α × (β ⊕ γ) → (α × β) ⊕ (α × γ)`.
 * Write a function that shows how 2 × _x_ = _x_ + _x_. It should have type `Bool × α → α ⊕ α`.
