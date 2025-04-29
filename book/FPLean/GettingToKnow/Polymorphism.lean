import VersoManual
import FPLean.Examples

open Verso.Genre Manual

open FPLean

example_module Examples.Intro

#doc (Manual) "Polymorphism" =>

Just as in most languages, types in Lean can take arguments.
For instance, the type {term}`List Nat` describes lists of natural numbers, {term}`List String` describes lists of strings, and {term}`List (List Point)` describes lists of lists of points.
This is very similar to {CSharp}`List<Nat>`, {CSharp}`List<String>`, or {CSharp}`List<List<Point>>` in a language like C# or Java.
Just as Lean uses a space to pass an argument to a function, it uses a space to pass an argument to a type.

In functional programming, the term _polymorphism_ typically refers to datatypes and definitions that take types as arguments.
This is different from the object-oriented programming community, where the term typically refers to subclasses that may override some behavior of their superclass.
In this book, “polymorphism” always refers to the first sense of the word.
These type arguments can be used in the datatype or definition, which allows the same datatype or definition to be used with any type that results from replacing the arguments' names with some other types.

:::paragraph
The {term}`Point.name` structure requires that both the {term}`Point.x` and {term}`Point.y` fields are {term}`Float.name`s.
There is, however, nothing about points that require a specific representation for each coordinate.
A polymorphic version of {term}`Point.name`, called {term}`PPoint.name`, can take a type as an argument, and then use that type for both fields:

{exampleDecl PPoint}

:::

Just as a function definition's arguments are written immediately after the name being defined, a structure's arguments are written immediately after the structure's name.
It is customary to use Greek letters to name type arguments in Lean when no more specific name suggests itself.
{term}`Type` is a type that describes other types, so {term}`Nat.name`, `List String`, and `PPoint Int` all have type `Type`.

:::paragraph
Just like {term}`List.name`, {term}`PPoint.name` can be used by providing a specific type as its argument:

{exampleDecl natPoint}

In this example, both fields are expected to be {term}`Nat.name`s.
Just as a function is called by replacing its argument variables with its argument values, providing {term}`PPoint.name` with the type {term}`Nat.name` as an argument yields a structure in which the fields {term}`PPoint.x` and {term}`PPoint.y` have the type {term}`Nat.name`, because the argument name {term}`PPoint.α` has been replaced by the argument type {term}`Nat.name`.
Types are ordinary expressions in Lean, so passing arguments to polymorphic types (like {term}`PPoint.name`) doesn't require any special syntax.
:::

:::paragraph
Definitions may also take types as arguments, which makes them polymorphic.
The function {term}`replaceX.name` replaces the {term}`PPoint.x` field of a {term}`PPoint.name` with a new value.
In order to allow {term}`replaceX.name` to work with _any_ polymorphic point, it must be polymorphic itself.
This is achieved by having its first argument be the type of the point's fields, with later arguments referring back to the first argument's name.

{exampleDecl replaceX}

In other words, when the types of the arguments {term}`replaceX.point` and {term}`replaceX.newX` mention {term}`replaceX.α`, they are referring to _whichever type was provided as the first argument_.
This is similar to the way that function argument names refer to the values that were provided when they occur in the function's body.
:::

:::paragraph

This can be seen by asking Lean to check the type of {term}`replaceX.name`, and then asking it to check the type of {term}`replaceXNatT.term`.

{exampleIn replaceXT}

{exampleInfo replaceXT}

This function type includes the _name_ of the first argument, and later arguments in the type refer back to this name.
Just as the value of a function application is found by replacing the argument name with the provided argument value in the function's body, the type of a function application is found by replacing the argument's name with the provided value in the function's return type.
Providing the first argument, {term}`Nat.name`, causes all occurrences of {term}`replaceX.α` in the remainder of the type to be replaced with {term}`Nat.name`:

{exampleIn replaceXNatT}

{exampleInfo replaceXNatT}

Because the remaining arguments are not explicitly named, no further substitution occurs as more arguments are provided:

{exampleIn replaceXNatOriginT}

{exampleInfo replaceXNatOriginT}

{exampleIn replaceXNatOriginFiveT}

{exampleInfo replaceXNatOriginFiveT}

:::

:::paragraph
The fact that the type of the whole function application expression was determined by passing a type as an argument has no bearing on the ability to evaluate it.

{exampleIn replaceXNatOriginFiveV}

{exampleInfo replaceXNatOriginFiveV}

:::

:::paragraph
Polymorphic functions work by taking a named type argument and having later types refer to the argument's name.
However, there's nothing special about type arguments that allows them to be named.
Given a datatype that represents positive or negative signs:

{exampleDecl Sign}

:::

:::paragraph
it is possible to write a function whose argument is a sign.
If the argument is positive, the function returns a {term}`Nat.name`, while if it's negative, it returns an {term}`Int.name`:

{exampleDecl posOrNegThree}

Because types are first class and can be computed using the ordinary rules of the Lean language, they can be computed by pattern-matching against a datatype.
When Lean is checking this function, it uses the fact that the {kw}`match`-expression in the function's body corresponds to the {kw}`match`-expression in the type to make {term}`Nat.name` be the expected type for the {term}`pos.name` case and to make {term}`Int.name` be the expected type for the {term}`neg.name` case.

:::

:::paragraph
Applying {term}`posOrNegThree.name` to {term}`Sign.pos.name` results in the argument name {term}`posOrNegThree.s` in both the body of the function and its return type being replaced by {term}`Sign.pos.name`.
Evaluation can occur both in the expression and its type:

{exampleEval posOrNegThreePos}

:::

# Linked Lists

:::paragraph
Lean's standard library includes a canonical linked list datatype, called {term}`List.name`, and special syntax that makes it more convenient to use.
Lists are written in square brackets.
For instance, a list that contains the prime numbers less than 10 can be written:

{exampleDecl primesUnder10}

:::

:::paragraph
Behind the scenes, {term}`fakeList` is an inductive datatype, defined like this:

{exampleDecl List}

The actual definition in the standard library is slightly different, because it uses features that have not yet been presented, but it is substantially similar.
This definition says that {term}`fakeList` takes a single type as its argument, just as {term}`PPoint.name` did.
This type is the type of the entries stored in the list.
According to the constructors, a {term}`List.rec` can be built with either {term}`fakeNil` or {term}`fakeCons`.
The constructor {term}`fakeNil` represents empty lists and the constructor {term}`fakeCons` is used for non-empty lists.
The first argument to {term}`fakeCons` is the head of the list, and the second argument is its tail.
A list that contains $`n` entries contains $`n` {term}`fakeCons` constructors, the last of which has {term}`fakeNil` as its tail.

:::

:::paragraph
The {term}`primesUnder10.name` example can be written more explicitly by using {term}`List.name`'s constructors directly:

{exampleDecl explicitPrimesUnder10}

These two definitions are completely equivalent, but {term}`primesUnder10.name` is much easier to read than {term}`explicitPrimesUnder10.name`.
:::

:::paragraph
Functions that consume {term}`List.name`s can be defined in much the same way as functions that consume {term}`Nat.name`s.
Indeed, one way to think of a linked list is as a {term}`Nat.name` that has an extra data field dangling off each {term}`succ.name` constructor.
From this point of view, computing the length of a list is the process of replacing each {term}`cons.name` with a {term}`succ.name` and the final {term}`nil.name` with a {term}`zero.name`.
Just as {term}`replaceX.name` took the type of the fields of the point as an argument, {term}`length1.name` takes the type of the list's entries.
For example, if the list contains strings, then the first argument is {term}`String.name`: {exampleEval 0}`length1EvalSummary`.
It should compute like this:

{exampleEval length1EvalSummary}

:::

:::paragraph

The definition of {term}`length1.name` is both polymorphic (because it takes the list entry type as an argument) and recursive (because it refers to itself).
Generally, functions follow the shape of the data: recursive datatypes lead to recursive functions, and polymorphic datatypes lead to polymorphic functions.

{exampleDecl length1}

:::

Names such as `xs` and `ys` are conventionally used to stand for lists of unknown values.
The `s` in the name indicates that they are plural, so they are pronounced “exes” and “whys” rather than “x s” and “y s”.

:::paragraph
To make it easier to read functions on lists, the bracket notation `[]` can be used to pattern-match against {term}`nil.name`, and an infix `::` can be used in place of {term}`cons.name`:

{exampleDecl length2}

:::

# Implicit Arguments

:::paragraph
Both {term}`replaceX.name` and {term}`length1.name` are somewhat bureaucratic to use, because the type argument is typically uniquely determined by the later values.
Indeed, in most languages, the compiler is perfectly capable of determining type arguments on its own, and only occasionally needs help from users.
This is also the case in Lean.
Arguments can be declared _implicit_ by wrapping them in curly braces instead of parentheses when defining a function.
For example, a version of {term}`replaceX.name` with an implicit type argument looks like this:

{exampleDecl replaceXImp}

It can be used with {term}`natOrigin.name` without providing {term}`Nat.name` explicitly, because Lean can _infer_ the value of {term}`replaceXImp.α` from the later arguments:

{exampleIn replaceXImpNat}

{exampleInfo replaceXImpNat}

:::

:::paragraph

Similarly, {term}`length1.name` can be redefined to take the entry type implicitly:

{exampleDecl lengthImp}

This {term}`lengthImp.name` function can be applied directly to {term}`primesUnder10.name`:

{exampleIn lengthImpPrimes}

{exampleInfo lengthImpPrimes}

:::

:::paragraph
In the standard library, Lean calls this function {term}`List.length.name`, which means that the dot syntax that is used for structure field access can also be used to find the length of a list:

{exampleIn lengthDotPrimes}

{exampleInfo lengthDotPrimes}

:::

:::paragraph
Just as C# and Java require type arguments to be provided explicitly from time to time, Lean is not always capable of finding implicit arguments.
In these cases, they can be provided using their names.
For example, a version of {term}`List.length.name` that only works for lists of integers can be specified by setting {term}`α.name` to {term}`Int.name`:

{exampleIn lengthExpNat}

{exampleInfo lengthExpNat}

:::

# More Built-In Datatypes

In addition to lists, Lean's standard library contains a number of other structures and inductive datatypes that can be used in a variety of contexts.

## `Option`
Not every list has a first entry—some lists are empty.
Many operations on collections may fail to find what they are looking for.
For instance, a function that finds the first entry in a list may not find any such entry.
It must therefore have a way to signal that there was no first entry.

Many languages have a {CSharp}`null` value that represents the absence of a value.
Instead of equipping existing types with a special {CSharp}`null` value, Lean provides a datatype called {term}`Option.name` that equips some other type with an indicator for missing values.
For instance, a nullable {term}`Int.name` is represented by {term}`Option Int`, and a nullable list of strings is represented by the type {term}`Option (List String)`.
Introducing a new type to represent nullability means that the type system ensures that checks for `null` cannot be forgotten, because an {term}`Option Int` can't be used in a context where an {term}`Int.name` is expected.

:::paragraph
{term}`fakeOption` has two constructors, called {term}`fakeSome` and {term}`fakeNone`, that respectively represent the non-null and null versions of the underlying type.
The non-null constructor, {term}`fakeSome`, contains the underlying value, while {term}`fakeNone` takes no arguments:

{exampleDecl Option}

:::

The {term}`fakeOption` type is very similar to nullable types in languages like C# and Kotlin, but it is not identical.
In these languages, if a type (say, {CSharp}`Boolean`) always refers to actual values of the type ({CSharp}`true` and {CSharp}`false`), the type {CSharp}`Boolean?` or {CSharp}`Nullable<Boolean>` additionally admits the {CSharp}`null` value.
Tracking this in the type system is very useful: the type checker and other tooling can help programmers remember to check for {CSharp}`null`, and APIs that explicitly describe nullability through type signatures are more informative than ones that don't.
However, these nullable types differ from Lean's {term}`fakeOption` in one very important way, which is that they don't allow multiple layers of optionality.
{exampleOut}`nullThree` can be constructed with {exampleIn}`nullOne`, {exampleIn}`nullTwo`, or {exampleIn}`nullThree`.
Kotlin, on the other hand, treats {Kotlin}`T??` as being equivalent to {Kotlin}`T?`.
This subtle difference is rarely relevant in practice, but it can matter from time to time.

:::paragraph
To find the first entry in a list, if it exists, use {term}`fakeHead?`.
The question mark is part of the name, and is not related to the use of question marks to indicate nullable types in C# or Kotlin.
In the definition of {term}`fakeHead?`, an underscore is used to represent the tail of the list.
In patterns, underscores match anything at all, but do not introduce variables to refer to the matched data.
Using underscores instead of names is a way to clearly communicate to readers that part of the input is ignored.

{exampleDecl headHuh}

:::

A Lean naming convention is to define operations that might fail in groups using the suffixes `?` for a version that returns an {term}`Option.name`, `!` for a version that crashes when provided with invalid input, and `D` for a version that returns a default value when the operation would otherwise fail.
Following this pattern, {term}`List.head.name` requires the caller to provide mathematical evidence that the list is not empty, {term}`List.head?.name` returns an {term}`Option.name`, {term}`List.head!.name` crashes the program when passed an empty list, and {term}`List.headD.name` takes a default value to return in case the list is empty.
The question mark and exclamation mark are part of the name, not special syntax, as Lean's naming rules are more liberal than many languages.

:::paragraph

Because {term}`head?.name` is defined in the `List` namespace, it can be used with accessor notation:

{exampleIn headSome}

{exampleInfo headSome}

However, attempting to test it on the empty list leads to two errors:

{exampleIn headNoneBad}

{exampleErrors headNoneBad}

:::

:::paragraph
This is because Lean was unable to fully determine the expression's type.
In particular, it could neither find the implicit type argument to {term}`List.head?.name`, nor the implicit type argument to {term}`List.nil.name`.
In Lean's output, `?m.XYZ` represents a part of a program that could not be inferred.
These unknown parts are called _metavariables_, and they occur in some error messages.
In order to evaluate an expression, Lean needs to be able to find its type, and the type was unavailable because the empty list does not have any entries from which the type can be found.
Explicitly providing a type allows Lean to proceed:

{exampleIn headNone}

{exampleInfo headNone}

The type can also be provided with a type annotation:

{exampleIn headNoneTwo}

{exampleInfo headNoneTwo}

The error messages provide a useful clue.
Both messages use the _same_ metavariable to describe the missing implicit argument, which means that Lean has determined that the two missing pieces will share a solution, even though it was unable to determine the actual value of the solution.

:::

## `Prod`

The {term}`Prod.name` structure, short for “Product”, is a generic way of joining two values together.
For instance, a {term}`Prod Nat String` contains a {term}`Nat.name` and a {term}`String.name`.
In other words, {term}`PPoint Nat` could be replaced by {term}`Prod Nat Nat`.
{term}`Prod.name` is very much like C#'s tuples, the {Kotlin}`Pair` and {Kotlin}`Triple` types in Kotlin, and {cpp}`tuple` in C++.
Many applications are best served by defining their own structures, even for simple cases like {term}`Point.name`, because using domain terminology can make it easier to read the code.
Additionally, defining structure types helps catch more errors by assigning different types to different domain concepts, preventing them from being mixed up.

On the other hand, there are some cases where it is not worth the overhead of defining a new type.
Additionally, some libraries are sufficiently generic that there is no more specific concept than "pair".
Finally, the standard library contains a variety of convenience functions that make it easier to work with the built-in pair type.

:::paragraph
The structure {term}`fakeProd` is defined with two type arguments:

{exampleDecl Prod}

:::

:::paragraph
Lists are used so frequently that there is special syntax to make them more readable.
For the same reason, both the product type and its constructor have special syntax.
The type {term}`αxβ.desugar` is typically written {term}`αxβ.sugar`, mirroring the usual notation for a Cartesian product of sets.
Similarly, the usual mathematical notation for pairs is available for {term}`Prod.name`.
In other words, instead of writing:

{exampleDecl fivesStruct}

it suffices to write:

{exampleDecl fives}

:::

:::paragraph

Both notations are right-associative.
This means that the following definitions are equivalent:

{exampleDecl sevens}

{exampleDecl sevensNested}

In other words, all products of more than two types, and their corresponding constructors, are actually nested products and nested pairs behind the scenes.

:::


## `Sum`

The {term}`Sum.name` datatype is a generic way of allowing a choice between values of two different types.
For instance, a {term}`Sum String Int` is either a {term}`String.name` or an {term}`Int.name`.
Like {term}`Prod.name`, {term}`Sum.name` should be used either when writing very generic code, for a very small section of code where there is no sensible domain-specific type, or when the standard library contains useful functions.
In most situations, it is more readable and maintainable to use a custom inductive type.

:::paragraph
Values of type {term}`Sumαβ.ex` are either the constructor {term}`fakeInl` applied to a value of type {term}`Sumαβ.α` or the constructor {term}`fakeInr` applied to a value of type {term}`Sumαβ.β`:

{exampleDecl Sum}

These names are abbreviations for “left injection” and “right injection”, respectively.
Just as the Cartesian product notation is used for {term}`Prod.name`, a “circled plus” notation is used for {term}`Sum.name`, so {term}`Sumαβ.sugar` is another way to write {term}`Sumαβ.ex`.
There is no special syntax for {term}`fakeSum.inl` and {term}`fakeSum.inr`.

:::

:::paragraph
As an example, if pet names can either be dog names or cat names, then a type for them can be introduced as a sum of strings:

{exampleDecl PetName}

In a real program, it would usually be better to define a custom inductive datatype for this purpose with informative constructor names.
Here, {term}`Sum.inl.name` is to be used for dog names, and {term}`Sum.inr.name` is to be used for cat names.
These constructors can be used to write a list of animal names:

{exampleDecl animals}

:::

:::paragraph
Pattern matching can be used to distinguish between the two constructors.
For instance, a function that counts the number of dogs in a list of animal names (that is, the number of {term}`Sum.inl.name` constructors) looks like this:

{exampleDecl howManyDogs}

Function calls are evaluated before infix operators, so {exampleIn}`howManyDogsAdd` is the same as {exampleOut}`howManyDogsAdd`.
As expected, {exampleIn}`dogCount` yields {exampleInfo}`dogCount`.
:::

## `Unit`

:::paragraph
{term}`fakeUnit` is a type with just one argumentless constructor, called {term}`fakeunit`.
In other words, it describes only a single value, which consists of said constructor applied to no arguments whatsoever.
{term}`fakeUnit` is defined as follows:

{exampleDecl Unit}

:::

:::paragraph
On its own, {term}`Unit.name` is not particularly useful.
However, in polymorphic code, it can be used as a placeholder for data that is missing.
For instance, the following inductive datatype represents arithmetic expressions:

{exampleDecl ArithExpr}

The type argument {term}`ArithExpr.ann` stands for annotations, and each constructor is annotated.
Expressions coming from a parser might be annotated with source locations, so a return type of {term}`ArithExpr SourcePos` ensures that the parser put a {term}`SourcePos.name` at each subexpression.
Expressions that don't come from the parser, however, will not have source locations, so their type can be {term}`ArithExpr Unit`.

:::

Additionally, because all Lean functions have arguments, zero-argument functions in other languages can be represented as functions that take a {term}`Unit.name` argument.
In a return position, the {term}`Unit.name` type is similar to {CSharp}`void` in languages derived from C.
In the C family, a function that returns {CSharp}`void` will return control to its caller, but it will not return any interesting value.
By being an intentionally uninteresting value, {term}`Unit.name` allows this to be expressed without requiring a special-purpose {CSharp}`void` feature in the type system.
Unit's constructor can be written as empty parentheses: {exampleIn}`unitParens` : {exampleOut}`unitParens`.

## `Empty`

The {term}`Empty.name` datatype has no constructors whatsoever.
Thus, it indicates unreachable code, because no series of calls can ever terminate with a value at type {term}`Empty.name`.

{term}`Empty.name` is not used nearly as often as {term}`Unit.name`.
However, it is useful in some specialized contexts.
Many polymorphic datatypes do not use all of their type arguments in all of their constructors.
For instance, {term}`Sum.inl.name` and {term}`Sum.inr.name` each use only one of {term}`Sum.name`'s type arguments.
Using {term}`Empty.name` as one of the type arguments to {term}`Sum.name` can rule out one of the constructors at a particular point in a program.
This can allow generic code to be used in contexts that have additional restrictions.

## Naming: Sums, Products, and Units

Generally speaking, types that offer multiple constructors are called _sum types_, while types whose single constructor takes multiple arguments are called _product types_.
These terms are related to sums and products used in ordinary arithmetic.
The relationship is easiest to see when the types involved contain a finite number of values.
If {term}`sizes.α` and {term}`sizes.β` are types that contain $`n` and $`k` distinct values, respectively, then {term}`sizes.sum` contains $`n + k` distinct values and {term}`sizes.prod` contains $`n \times k` distinct values.
For instance, {term}`Bool.name` has two values: {term}`true` and {term}`false`, and {term}`Unit.name` has one value: {term}`Unit.unit.name`.
The product {term}`Bool × Unit` has the two values {term}`BoolxUnit.vals.one` and {term}`BoolxUnit.vals.two`, and the sum {term}`Bool ⊕ Unit` has the three values {term}`BooloUnit.vals.one`, {term}`BooloUnit.vals.two`, and {term}`BooloUnit.vals.three`.
Similarly, $`2 \times 1 = 2`, and $`2 + 1 = 3`.

# Messages You May Meet

:::paragraph
Not all definable structures or inductive types can have the type {term}`Type`.
In particular, if a constructor takes an arbitrary type as an argument, then the inductive type must have a different type.
These errors usually state something about “universe levels”.
For example, for this inductive type:

{exampleIn TypeInType}

Lean gives the following error:

{exampleError TypeInType}

A later chapter describes why this is the case, and how to modify definitions to make them work.
For now, try making the type an argument to the inductive type as a whole, rather than to the constructor.
:::

:::paragraph
Similarly, if a constructor's argument is a function that takes the datatype being defined as an argument, then the definition is rejected.
For example:

{exampleIn Positivity}

yields the message:

{exampleError Positivity}

For technical reasons, allowing these datatypes could make it possible to undermine Lean's internal logic, making it unsuitable for use as a theorem prover.
:::

:::paragraph
Recursive functions that take two parameters should not match against the pair, but rather match each parameter independently.
Otherwise, the mechanism in Lean that checks whether recursive calls are made on smaller values is unable to see the connection between the input value and the argument in the recursive call.
For example, this function that determines whether two lists have the same length is rejected:

{exampleIn sameLengthPair}

The error message is:

{exampleError sameLengthPair}

The problem can be fixed through nested pattern matching:

{exampleDecl sameLengthOk1}

[Simultaneous matching](conveniences.md#simultaneous-matching), described in the next section, is another way to solve the problem that is often more elegant.
:::

:::paragraph
Forgetting an argument to an inductive type can also yield a confusing message.
For example, when the argument {term}`MissingTypeArg.α` is not passed to {term}`MyType.name` in {term}`MyType.ctor.name`'s type:

{exampleIn MissingTypeArg}

Lean replies with the following error:

{exampleError MissingTypeArg}

The error message is saying that {term}`MyType.name`'s type, which is {term}`Type→Type`, does not itself describe types.
{term}`MyType.name` requires an argument to become an actual honest-to-goodness type.

:::

:::paragraph
The same message can appear when type arguments are omitted in other contexts, such as in a type signature for a definition:

{exampleDecl MyTypeDef}

{exampleIn MissingTypeArg2}

{exampleError MissingTypeArg2}

:::

# Exercises

 * Write a function to find the last entry in a list. It should return an {term}`Option.name`.
 * Write a function that finds the first entry in a list that satisfies a given predicate. Start the definition with {exampleDecl}`List.findFirst?Ex`.
 * Write a function {term}`Prod.switch` that switches the two fields in a pair for each other. Start the definition with {exampleDecl}`Prod.switchEx`.
 * Rewrite the {term}`PetName.name` example to use a custom datatype and compare it to the version that uses {term}`Sum.name`.
 * Write a function {term}`zip` that combines two lists into a list of pairs. The resulting list should be as long as the shortest input list. Start the definition with {exampleDecl}`zipEx`.
 * Write a polymorphic function `take` that returns the first $`n` entries in a list, where $`n` is a {term}`Nat.name`. If the list contains fewer than $`n` entries, then the resulting list should be the entire input list. {exampleIn}`takeThree` should yield {exampleInfo}`takeThree`, and {exampleIn}`takeOne` should yield {exampleInfo}`takeOne`.
 * Using the analogy between types and arithmetic, write a function that distributes products over sums. In other words, it should have type {term}`distr.one`.
 * Using the analogy between types and arithmetic, write a function that turns multiplication by two into a sum. In other words, it should have type {term}`distr.two`.
