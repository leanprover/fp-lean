import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "Polymorphism" =>
%%%
tag := "polymorphism"
%%%

Just as in most languages, types in Lean can take arguments.
For instance, the type {anchorTerm fragments}`List Nat` describes lists of natural numbers, {anchorTerm fragments}`List String` describes lists of strings, and {anchorTerm fragments}`List (List Point)` describes lists of lists of points.
This is very similar to {CSharp}`List<Nat>`, {CSharp}`List<String>`, or {CSharp}`List<List<Point>>` in a language like C# or Java.
Just as Lean uses a space to pass an argument to a function, it uses a space to pass an argument to a type.

In functional programming, the term _polymorphism_ typically refers to datatypes and definitions that take types as arguments.
This is different from the object-oriented programming community, where the term typically refers to subclasses that may override some behavior of their superclass.
In this book, “polymorphism” always refers to the first sense of the word.
These type arguments can be used in the datatype or definition, which allows the same datatype or definition to be used with any type that results from replacing the arguments' names with some other types.

:::paragraph
The {anchorName Point}`Point` structure requires that both the {anchorName Point}`x` and {anchorName Point}`y` fields are {anchorName Point}`Float`s.
There is, however, nothing about points that require a specific representation for each coordinate.
A polymorphic version of {anchorName Point}`Point`, called {anchorName PPoint}`PPoint`, can take a type as an argument, and then use that type for both fields:

```anchor PPoint
structure PPoint (α : Type) where
  x : α
  y : α
```

:::

Just as a function definition's arguments are written immediately after the name being defined, a structure's arguments are written immediately after the structure's name.
It is customary to use Greek letters to name type arguments in Lean when no more specific name suggests itself.
{anchorTerm PPoint}`Type` is a type that describes other types, so {anchorName Nat}`Nat`, {anchorTerm fragments}`List String`, and {anchorTerm fragments}`PPoint Int` all have type {anchorTerm PPoint}`Type`.

:::paragraph
Just like {anchorName fragments}`List`, {anchorName PPoint}`PPoint` can be used by providing a specific type as its argument:

```anchor natPoint
def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }
```

In this example, both fields are expected to be {anchorName natPoint}`Nat`s.
Just as a function is called by replacing its argument variables with its argument values, providing {anchorName PPoint}`PPoint` with the type {anchorName fragments}`Nat` as an argument yields a structure in which the fields {anchorName PPoint}`x` and {anchorName PPoint}`y` have the type {anchorName fragments}`Nat`, because the argument name {anchorName PPoint}`α` has been replaced by the argument type {anchorName fragments}`Nat`.
Types are ordinary expressions in Lean, so passing arguments to polymorphic types (like {anchorName PPoint}`PPoint`) doesn't require any special syntax.
:::

:::paragraph
Definitions may also take types as arguments, which makes them polymorphic.
The function {anchorName replaceX}`replaceX` replaces the {anchorName replaceX}`x` field of a {anchorName replaceX}`PPoint` with a new value.
In order to allow {anchorName replaceX}`replaceX` to work with _any_ polymorphic point, it must be polymorphic itself.
This is achieved by having its first argument be the type of the point's fields, with later arguments referring back to the first argument's name.

```anchor replaceX
def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
```

In other words, when the types of the arguments {anchorName replaceX}`point` and {anchorName replaceX}`newX` mention {anchorName replaceX}`α`, they are referring to _whichever type was provided as the first argument_.
This is similar to the way that function argument names refer to the values that were provided when they occur in the function's body.
:::

:::paragraph

This can be seen by asking Lean to check the type of {anchorName replaceX}`replaceX`, and then asking it to check the type of {anchorTerm replaceXNatOriginFiveT}`replaceX Nat`.

```anchorTerm replaceXT
#check (replaceX)
```

```anchorInfo replaceXT
replaceX : (α : Type) → PPoint α → α → PPoint α
```

This function type includes the _name_ of the first argument, and later arguments in the type refer back to this name.
Just as the value of a function application is found by replacing the argument name with the provided argument value in the function's body, the type of a function application is found by replacing the argument's name with the provided value in the function's return type.
Providing the first argument, {anchorName replaceXNatT}`Nat`, causes all occurrences of {anchorName replaceX}`α` in the remainder of the type to be replaced with {anchorName replaceXNatT}`Nat`:

```anchorTerm replaceXNatT
#check replaceX Nat
```

```anchorInfo replaceXNatT
replaceX Nat : PPoint Nat → Nat → PPoint Nat
```

Because the remaining arguments are not explicitly named, no further substitution occurs as more arguments are provided:

```anchorTerm replaceXNatOriginT
#check replaceX Nat natOrigin
```

```anchorInfo replaceXNatOriginT
replaceX Nat natOrigin : Nat → PPoint Nat
```

```anchorTerm replaceXNatOriginFiveT
#check replaceX Nat natOrigin 5
```

```anchorInfo replaceXNatOriginFiveT
replaceX Nat natOrigin 5 : PPoint Nat
```

:::

:::paragraph
The fact that the type of the whole function application expression was determined by passing a type as an argument has no bearing on the ability to evaluate it.

```anchorTerm replaceXNatOriginFiveV
#eval replaceX Nat natOrigin 5
```

```anchorInfo replaceXNatOriginFiveV
{ x := 5, y := 0 }
```

:::

:::paragraph
Polymorphic functions work by taking a named type argument and having later types refer to the argument's name.
However, there's nothing special about type arguments that allows them to be named.
Given a datatype that represents positive or negative signs:

```anchor Sign
inductive Sign where
  | pos
  | neg
```

:::

:::paragraph
it is possible to write a function whose argument is a sign.
If the argument is positive, the function returns a {anchorName posOrNegThree}`Nat`, while if it's negative, it returns an {anchorName posOrNegThree}`Int`:

```anchor posOrNegThree
def posOrNegThree (s : Sign) :
    match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)
```

Because types are first class and can be computed using the ordinary rules of the Lean language, they can be computed by pattern-matching against a datatype.
When Lean is checking this function, it uses the fact that the {kw}`match`-expression in the function's body corresponds to the {kw}`match`-expression in the type to make {anchorName posOrNegThree}`Nat` be the expected type for the {anchorName Sign}`pos` case and to make {anchorName posOrNegThree}`Int` be the expected type for the {anchorName Sign}`neg` case.

:::

:::paragraph
Applying {anchorName posOrNegThree}`posOrNegThree` to {anchorName Sign}`pos` results in the argument name {anchorName posOrNegThree}`s` in both the body of the function and its return type being replaced by {anchorName Sign}`pos`.
Evaluation can occur both in the expression and its type:

```anchorEvalSteps posOrNegThreePos
(posOrNegThree Sign.pos :
 match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
===>
((match Sign.pos with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)) :
 match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
===>
((3 : Nat) : Nat)
===>
3
```

:::

# Linked Lists
%%%
tag := "linked-lists"
%%%

:::paragraph
Lean's standard library includes a canonical linked list datatype, called {anchorName fragments}`List`, and special syntax that makes it more convenient to use.
Lists are written in square brackets.
For instance, a list that contains the prime numbers less than 10 can be written:

```anchor primesUnder10
def primesUnder10 : List Nat := [2, 3, 5, 7]
```

:::

:::paragraph
Behind the scenes, {anchorName List}`List` is an inductive datatype, defined like this:

```anchor List
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
```

The actual definition in the standard library is slightly different, because it uses features that have not yet been presented, but it is substantially similar.
This definition says that {anchorName List}`List` takes a single type as its argument, just as {anchorName PPoint}`PPoint` did.
This type is the type of the entries stored in the list.
According to the constructors, a {anchorTerm List}`List α` can be built with either {anchorName List}`nil` or {anchorName List}`cons`.
The constructor {anchorName List}`nil` represents empty lists and the constructor {anchorName List}`cons` is used for non-empty lists.
The first argument to {anchorName List}`cons` is the head of the list, and the second argument is its tail.
A list that contains $`n` entries contains $`n` {anchorName List}`cons` constructors, the last of which has {anchorName List}`nil` as its tail.

:::

:::paragraph
The {anchorName primesUnder10}`primesUnder10` example can be written more explicitly by using {anchorName List}`List`'s constructors directly:

```anchor explicitPrimesUnder10
def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))
```

These two definitions are completely equivalent, but {anchorName primesUnder10}`primesUnder10` is much easier to read than {anchorName explicitPrimesUnder10}`explicitPrimesUnder10`.
:::

:::paragraph
Functions that consume {anchorName List}`List`s can be defined in much the same way as functions that consume {anchorName Nat}`Nat`s.
Indeed, one way to think of a linked list is as a {anchorName Nat}`Nat` that has an extra data field dangling off each {anchorName Nat}`succ` constructor.
From this point of view, computing the length of a list is the process of replacing each {anchorName List}`cons` with a {anchorName Nat}`succ` and the final {anchorName List}`nil` with a {anchorName Nat}`zero`.
Just as {anchorName replaceX}`replaceX` took the type of the fields of the point as an argument, {anchorName length1EvalSummary}`length` takes the type of the list's entries.
For example, if the list contains strings, then the first argument is {anchorName length1EvalSummary}`String`: {anchorEvalStep length1EvalSummary 0}`length String ["Sourdough", "bread"]`.
It should compute like this:

```anchorEvalSteps length1EvalSummary
length String ["Sourdough", "bread"]
===>
length String (List.cons "Sourdough" (List.cons "bread" List.nil))
===>
Nat.succ (length String (List.cons "bread" List.nil))
===>
Nat.succ (Nat.succ (length String List.nil))
===>
Nat.succ (Nat.succ Nat.zero)
===>
2
```

:::

:::paragraph

The definition of {anchorName length1}`length` is both polymorphic (because it takes the list entry type as an argument) and recursive (because it refers to itself).
Generally, functions follow the shape of the data: recursive datatypes lead to recursive functions, and polymorphic datatypes lead to polymorphic functions.

```anchor length1
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)
```

:::

Names such as {lit}`xs` and {lit}`ys` are conventionally used to stand for lists of unknown values.
The {lit}`s` in the name indicates that they are plural, so they are pronounced “exes” and “whys” rather than “x s” and “y s”.

:::paragraph
To make it easier to read functions on lists, the bracket notation {anchorTerm length2}`[]` can be used to pattern-match against {anchorName List}`nil`, and an infix {anchorTerm length2}`::` can be used in place of {anchorName List}`cons`:

```anchor length2
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length α ys)
```

:::

# Implicit Arguments
%%%
tag := "implicit-parameters"
%%%

:::paragraph
Both {anchorName replaceX}`replaceX` and {anchorName length1}`length` are somewhat bureaucratic to use, because the type argument is typically uniquely determined by the later values.
Indeed, in most languages, the compiler is perfectly capable of determining type arguments on its own, and only occasionally needs help from users.
This is also the case in Lean.
Arguments can be declared _implicit_ by wrapping them in curly braces instead of parentheses when defining a function.
For example, a version of {anchorName replaceXImp}`replaceX` with an implicit type argument looks like this:

```anchor replaceXImp
def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
```

It can be used with {anchorName replaceXImpNat}`natOrigin` without providing {anchorName NatDoubleFour}`Nat` explicitly, because Lean can _infer_ the value of {anchorName replaceXImp}`α` from the later arguments:

```anchor replaceXImpNat
#eval replaceX natOrigin 5
```

```anchorInfo replaceXImpNat
{ x := 5, y := 0 }
```

:::

:::paragraph

Similarly, {anchorName lengthImp}`length` can be redefined to take the entry type implicitly:

```anchor lengthImp
def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

This {anchorName lengthImp}`length` function can be applied directly to {anchorName lengthImpPrimes}`primesUnder10`:

```anchor lengthImpPrimes
#eval length primesUnder10
```

```anchorInfo lengthImpPrimes
4
```

:::

:::paragraph
In the standard library, Lean calls this function {anchorName lengthExpNat}`List.length`, which means that the dot syntax that is used for structure field access can also be used to find the length of a list:

```anchor lengthDotPrimes
#eval primesUnder10.length
```

```anchorInfo lengthDotPrimes
4
```

:::

:::paragraph
Just as C# and Java require type arguments to be provided explicitly from time to time, Lean is not always capable of finding implicit arguments.
In these cases, they can be provided using their names.
For example, a version of {anchorName lengthExpNat}`List.length` that only works for lists of integers can be specified by setting {anchorTerm lengthExpNat}`α` to {anchorName lengthExpNat}`Int`:

```anchor lengthExpNat
#check List.length (α := Int)
```

```anchorInfo lengthExpNat
List.length : List Int → Nat
```

:::

# More Built-In Datatypes
%%%
tag := "more-built-in-types"
%%%

In addition to lists, Lean's standard library contains a number of other structures and inductive datatypes that can be used in a variety of contexts.

## {lit}`Option`
%%%
tag := "Option"
%%%
Not every list has a first entry—some lists are empty.
Many operations on collections may fail to find what they are looking for.
For instance, a function that finds the first entry in a list may not find any such entry.
It must therefore have a way to signal that there was no first entry.

Many languages have a {CSharp}`null` value that represents the absence of a value.
Instead of equipping existing types with a special {CSharp}`null` value, Lean provides a datatype called {anchorName Option}`Option` that equips some other type with an indicator for missing values.
For instance, a nullable {anchorName fragments}`Int` is represented by {anchorTerm nullOne}`Option Int`, and a nullable list of strings is represented by the type {anchorTerm fragments}`Option (List String)`.
Introducing a new type to represent nullability means that the type system ensures that checks for {CSharp}`null` cannot be forgotten, because an {anchorTerm nullOne}`Option Int` can't be used in a context where an {anchorName nullOne}`Int` is expected.

:::paragraph
{anchorName Option}`Option` has two constructors, called {anchorName Option}`some` and {anchorName Option}`none`, that respectively represent the non-null and null versions of the underlying type.
The non-null constructor, {anchorName Option}`some`, contains the underlying value, while {anchorName Option}`none` takes no arguments:

```anchor Option
inductive Option (α : Type) : Type where
  | none : Option α
  | some (val : α) : Option α
```

:::

The {anchorName Option}`Option` type is very similar to nullable types in languages like C# and Kotlin, but it is not identical.
In these languages, if a type (say, {CSharp}`Boolean`) always refers to actual values of the type ({CSharp}`true` and {CSharp}`false`), the type {CSharp}`Boolean?` or {CSharp}`Nullable<Boolean>` additionally admits the {CSharp}`null` value.
Tracking this in the type system is very useful: the type checker and other tooling can help programmers remember to check for {CSharp}`null`, and APIs that explicitly describe nullability through type signatures are more informative than ones that don't.
However, these nullable types differ from Lean's {anchorName Option}`Option` in one very important way, which is that they don't allow multiple layers of optionality.
{anchorTerm nullThree}`Option (Option Int)` can be constructed with {anchorTerm nullOne}`none`, {anchorTerm nullTwo}`some none`, or {anchorTerm nullThree}`some (some 360)`.
Kotlin, on the other hand, treats {Kotlin}`T??` as being equivalent to {Kotlin}`T?`.
This subtle difference is rarely relevant in practice, but it can matter from time to time.

:::paragraph
To find the first entry in a list, if it exists, use {anchorName headHuh}`List.head?`.
The question mark is part of the name, and is not related to the use of question marks to indicate nullable types in C# or Kotlin.
In the definition of {anchorName headHuh}`List.head?`, an underscore is used to represent the tail of the list.
In patterns, underscores match anything at all, but do not introduce variables to refer to the matched data.
Using underscores instead of names is a way to clearly communicate to readers that part of the input is ignored.

```anchor headHuh
def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y
```

:::

A Lean naming convention is to define operations that might fail in groups using the suffixes {lit}`?` for a version that returns an {anchorName Option}`Option`, {lit}`!` for a version that crashes when provided with invalid input, and {lit}`D` for a version that returns a default value when the operation would otherwise fail.
Following this pattern, {anchorName fragments}`List.head` requires the caller to provide mathematical evidence that the list is not empty, {anchorName fragments}`List.head?` returns an {anchorName Option}`Option`, {anchorName fragments}`List.head!` crashes the program when passed an empty list, and {anchorName fragments}`List.headD` takes a default value to return in case the list is empty.
The question mark and exclamation mark are part of the name, not special syntax, as Lean's naming rules are more liberal than many languages.

:::paragraph

Because {anchorName fragments}`head?` is defined in the {lit}`List` namespace, it can be used with accessor notation:

```anchor headSome
#eval primesUnder10.head?
```

```anchorInfo headSome
some 2
```

However, attempting to test it on the empty list leads to two errors:

```anchor headNoneBad
#eval [].head?
```

```anchorError headNoneBad
don't know how to synthesize implicit argument 'α'
  @List.nil ?m.41782
context:
⊢ Type ?u.41779
```

```anchorError headNoneBad
don't know how to synthesize implicit argument 'α'
  @_root_.List.head? ?m.41782 []
context:
⊢ Type ?u.41779
```

:::

:::paragraph
This is because Lean was unable to fully determine the expression's type.
In particular, it could neither find the implicit type argument to {anchorName fragments}`List.head?`, nor the implicit type argument to {anchorName fragments}`List.nil`.
In Lean's output, {lit}`?m.XYZ` represents a part of a program that could not be inferred.
These unknown parts are called _metavariables_, and they occur in some error messages.
In order to evaluate an expression, Lean needs to be able to find its type, and the type was unavailable because the empty list does not have any entries from which the type can be found.
Explicitly providing a type allows Lean to proceed:

```anchor headNone
#eval [].head? (α := Int)
```

```anchorInfo headNone
none
```

The type can also be provided with a type annotation:

```anchor headNoneTwo
#eval ([] : List Int).head?
```

```anchorInfo headNoneTwo
none
```

The error messages provide a useful clue.
Both messages use the _same_ metavariable to describe the missing implicit argument, which means that Lean has determined that the two missing pieces will share a solution, even though it was unable to determine the actual value of the solution.

:::

## {lit}`Prod`
%%%
tag := "prod"
%%%

The {anchorName Prod}`Prod` structure, short for “Product”, is a generic way of joining two values together.
For instance, a {anchorTerm fragments}`Prod Nat String` contains a {anchorName fragments}`Nat` and a {anchorName fragments}`String`.
In other words, {anchorTerm natPoint}`PPoint Nat` could be replaced by {anchorTerm fragments}`Prod Nat Nat`.
{anchorName fragments}`Prod` is very much like C#'s tuples, the {Kotlin}`Pair` and {Kotlin}`Triple` types in Kotlin, and {cpp}`tuple` in C++.
Many applications are best served by defining their own structures, even for simple cases like {anchorName Point}`Point`, because using domain terminology can make it easier to read the code.
Additionally, defining structure types helps catch more errors by assigning different types to different domain concepts, preventing them from being mixed up.

On the other hand, there are some cases where it is not worth the overhead of defining a new type.
Additionally, some libraries are sufficiently generic that there is no more specific concept than “pair”.
Finally, the standard library contains a variety of convenience functions that make it easier to work with the built-in pair type.

:::paragraph
The structure {anchorName Prod}`Prod` is defined with two type arguments:

```anchor Prod
structure Prod (α : Type) (β : Type) : Type where
  fst : α
  snd : β
```

:::

:::paragraph
Lists are used so frequently that there is special syntax to make them more readable.
For the same reason, both the product type and its constructor have special syntax.
The type {anchorTerm ProdSugar}`Prod α β` is typically written {anchorTerm ProdSugar}`α × β`, mirroring the usual notation for a Cartesian product of sets.
Similarly, the usual mathematical notation for pairs is available for {anchorName ProdSugar}`Prod`.
In other words, instead of writing:

```anchor fivesStruct
def fives : String × Int := { fst := "five", snd := 5 }
```

it suffices to write:

```anchor fives
def fives : String × Int := ("five", 5)
```

:::

:::paragraph

Both notations are right-associative.
This means that the following definitions are equivalent:

```anchor sevens
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
```

```anchor sevensNested
def sevens : String × (Int × Nat) := ("VII", (7, 4 + 3))
```

In other words, all products of more than two types, and their corresponding constructors, are actually nested products and nested pairs behind the scenes.

:::


## {anchorName Sum}`Sum`
%%%
tag := "Sum"
%%%

The {anchorName Sum}`Sum` datatype is a generic way of allowing a choice between values of two different types.
For instance, a {anchorTerm fragments}`Sum String Int` is either a {anchorName fragments}`String` or an {anchorName fragments}`Int`.
Like {anchorName Prod}`Prod`, {anchorName Sum}`Sum` should be used either when writing very generic code, for a very small section of code where there is no sensible domain-specific type, or when the standard library contains useful functions.
In most situations, it is more readable and maintainable to use a custom inductive type.

:::paragraph
Values of type {anchorTerm Sumαβ}`Sum α β` are either the constructor {anchorName Sum}`inl` applied to a value of type {anchorName Sum}`α` or the constructor {anchorName Sum}`inr` applied to a value of type {anchorName Sum}`β`:

```anchor Sum
inductive Sum (α : Type) (β : Type) : Type where
  | inl : α → Sum α β
  | inr : β → Sum α β
```

These names are abbreviations for “left injection” and “right injection”, respectively.
Just as the Cartesian product notation is used for {anchorName Prod}`Prod`, a “circled plus” notation is used for {anchorName SumSugar}`Sum`, so {anchorTerm SumSugar}`α ⊕ β` is another way to write {anchorTerm SumSugar}`Sum α β`.
There is no special syntax for {anchorName FakeSum}`Sum.inl` and {anchorName FakeSum}`Sum.inr`.

:::

:::paragraph
As an example, if pet names can either be dog names or cat names, then a type for them can be introduced as a sum of strings:

```anchor PetName
def PetName : Type := String ⊕ String
```

In a real program, it would usually be better to define a custom inductive datatype for this purpose with informative constructor names.
Here, {anchorName animals}`Sum.inl` is to be used for dog names, and {anchorName animals}`Sum.inr` is to be used for cat names.
These constructors can be used to write a list of animal names:

```anchor animals
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi",
   Sum.inl "Rex", Sum.inr "Floof"]
```

:::

:::paragraph
Pattern matching can be used to distinguish between the two constructors.
For instance, a function that counts the number of dogs in a list of animal names (that is, the number of {anchorName howManyDogs}`Sum.inl` constructors) looks like this:

```anchor howManyDogs
def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets
```

Function calls are evaluated before infix operators, so {anchorTerm howManyDogsAdd}`howManyDogs morePets + 1` is the same as {anchorTerm howManyDogsAdd}`(howManyDogs morePets) + 1`.
As expected, {anchor dogCount}`#eval howManyDogs animals` yields {anchorInfo dogCount}`3`.
:::

## {anchorName Unit}`Unit`
%%%
tag := "Unit"
%%%

:::paragraph
{anchorName Unit}`Unit` is a type with just one argumentless constructor, called {anchorName Unit}`unit`.
In other words, it describes only a single value, which consists of said constructor applied to no arguments whatsoever.
{anchorName Unit}`Unit` is defined as follows:

```anchor Unit
inductive Unit : Type where
  | unit : Unit
```

:::

:::paragraph
On its own, {anchorName Unit}`Unit` is not particularly useful.
However, in polymorphic code, it can be used as a placeholder for data that is missing.
For instance, the following inductive datatype represents arithmetic expressions:

```anchor ArithExpr
inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
```

The type argument {anchorName ArithExpr}`ann` stands for annotations, and each constructor is annotated.
Expressions coming from a parser might be annotated with source locations, so a return type of {anchorTerm ArithExprEx}`ArithExpr SourcePos` ensures that the parser put a {anchorName ArithExprEx}`SourcePos` at each subexpression.
Expressions that don't come from the parser, however, will not have source locations, so their type can be {anchorTerm ArithExprEx}`ArithExpr Unit`.

:::

Additionally, because all Lean functions have arguments, zero-argument functions in other languages can be represented as functions that take a {anchorName ArithExprEx}`Unit` argument.
In a return position, the {anchorName ArithExprEx}`Unit` type is similar to {CSharp}`void` in languages derived from C.
In the C family, a function that returns {CSharp}`void` will return control to its caller, but it will not return any interesting value.
By being an intentionally uninteresting value, {anchorName ArithExprEx}`Unit` allows this to be expressed without requiring a special-purpose {CSharp}`void` feature in the type system.
Unit's constructor can be written as empty parentheses: {anchorTerm unitParens}`() : Unit`.

## {lit}`Empty`
%%%
tag := "Empty"
%%%

The {anchorName fragments}`Empty` datatype has no constructors whatsoever.
Thus, it indicates unreachable code, because no series of calls can ever terminate with a value at type {anchorName fragments}`Empty`.

{anchorName fragments}`Empty` is not used nearly as often as {anchorName fragments}`Unit`.
However, it is useful in some specialized contexts.
Many polymorphic datatypes do not use all of their type arguments in all of their constructors.
For instance, {anchorName animals}`Sum.inl` and {anchorName animals}`Sum.inr` each use only one of {anchorName fragments}`Sum`'s type arguments.
Using {anchorName fragments}`Empty` as one of the type arguments to {anchorName fragments}`Sum` can rule out one of the constructors at a particular point in a program.
This can allow generic code to be used in contexts that have additional restrictions.

## Naming: Sums, Products, and Units
%%%
tag := "sum-products-units"
%%%

Generally speaking, types that offer multiple constructors are called _sum types_, while types whose single constructor takes multiple arguments are called {deftech}_product types_.
These terms are related to sums and products used in ordinary arithmetic.
The relationship is easiest to see when the types involved contain a finite number of values.
If {anchorName SumProd}`α` and {anchorName SumProd}`β` are types that contain $`n` and $`k` distinct values, respectively, then {anchorTerm SumProd}`α ⊕ β` contains $`n + k` distinct values and {anchorTerm SumProd}`α × β` contains $`n \times k` distinct values.
For instance, {anchorName fragments}`Bool` has two values: {anchorName BoolNames}`true` and {anchorName BoolNames}`false`, and {anchorName Unit}`Unit` has one value: {anchorName BooloUnit}`Unit.unit`.
The product {anchorTerm fragments}`Bool × Unit` has the two values {anchorTerm BoolxUnit}`(true, Unit.unit)` and {anchorTerm BoolxUnit}`(false, Unit.unit)`, and the sum {anchorTerm fragments}`Bool ⊕ Unit` has the three values {anchorTerm BooloUnit}`Sum.inl true`, {anchorTerm BooloUnit}`Sum.inl false`, and {anchorTerm BooloUnit}`Sum.inr Unit.unit`.
Similarly, $`2 \times 1 = 2`, and $`2 + 1 = 3`.

# Messages You May Meet
%%%
tag := "polymorphism-messages"
%%%

:::paragraph
Not all definable structures or inductive types can have the type {anchorTerm Prod}`Type`.
In particular, if a constructor takes an arbitrary type as an argument, then the inductive type must have a different type.
These errors usually state something about “universe levels”.
For example, for this inductive type:

```anchor TypeInType
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType
```

Lean gives the following error:

```anchorError TypeInType
Invalid universe level in constructor `MyType.ctor`: Parameter `α` has type
  Type
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
```

A later chapter describes why this is the case, and how to modify definitions to make them work.
For now, try making the type an argument to the inductive type as a whole, rather than to the constructor.
:::

:::paragraph
Similarly, if a constructor's argument is a function that takes the datatype being defined as an argument, then the definition is rejected.
For example:

```anchor Positivity
inductive MyType : Type where
  | ctor : (MyType → Int) → MyType
```

yields the message:

```anchorError Positivity
(kernel) arg #1 of 'MyType.ctor' has a non positive occurrence of the datatypes being declared
```

For technical reasons, allowing these datatypes could make it possible to undermine Lean's internal logic, making it unsuitable for use as a theorem prover.
:::

:::paragraph
Recursive functions that take two parameters should not match against the pair, but rather match each parameter independently.
Otherwise, the mechanism in Lean that checks whether recursive calls are made on smaller values is unable to see the connection between the input value and the argument in the recursive call.
For example, this function that determines whether two lists have the same length is rejected:

```anchor sameLengthPair
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _ => false
```

The error message is:

```anchorError sameLengthPair
fail to show termination for
  sameLength
with errors
failed to infer structural recursion:
Not considering parameter α of sameLength:
  it is unchanged in the recursive calls
Not considering parameter β of sameLength:
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    sameLength xs' ys'
Cannot use parameter ys:
  failed to eliminate recursive application
    sameLength xs' ys'


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
              xs ys
1) 1760:28-46  ?  ?
Please use `termination_by` to specify a decreasing measure.
```

The problem can be fixed through nested pattern matching:

```anchor sameLengthOk1
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs with
  | [] =>
    match ys with
    | [] => true
    | _ => false
  | x :: xs' =>
    match ys with
    | y :: ys' => sameLength xs' ys'
    | _ => false
```

{ref "simultaneous-matching"}[Simultaneous matching], described in the next section, is another way to solve the problem that is often more elegant.
:::

:::paragraph
Forgetting an argument to an inductive type can also yield a confusing message.
For example, when the argument {anchorName MissingTypeArg}`α` is not passed to {anchorName MissingTypeArg}`MyType` in {anchorTerm MissingTypeArg}`ctor`'s type:

```anchor MissingTypeArg
inductive MyType (α : Type) : Type where
  | ctor : α → MyType
```

Lean replies with the following error:

```anchorError MissingTypeArg
type expected, got
  (MyType : Type → Type)
```

The error message is saying that {anchorName MissingTypeArg}`MyType`'s type, which is {anchorTerm MissingTypeArgT}`Type → Type`, does not itself describe types.
{anchorName MissingTypeArg}`MyType` requires an argument to become an actual honest-to-goodness type.

:::

:::paragraph
The same message can appear when type arguments are omitted in other contexts, such as in a type signature for a definition:

```anchor MyTypeDef
inductive MyType (α : Type) : Type where
  | ctor : α → MyType α
```

```anchor MissingTypeArg2
def ofFive : MyType := ctor 5
```

```anchorError MissingTypeArg2
type expected, got
  (MyType : Type → Type)
```

:::

:::paragraph
Evaluating expressions that use polymorphic types may trigger a situation in which Lean is incapable of displaying a value.
The {anchorTerm evalAxe}`#eval` command evaluates the provided expression, using the expression's type to determine how to display the result.
For some types, such as functions, this process fails, but Lean is perfectly capable of automatically generating display code for most other types.
There is no need, for example, to provide Lean with any specific display code for {anchorName WoodSplittingTool}`WoodSplittingTool`:
```anchor WoodSplittingTool
inductive WoodSplittingTool where
  | axe
  | maul
  | froe
```
```anchor evalAxe
#eval WoodSplittingTool.axe
```
```anchorInfo evalAxe
WoodSplittingTool.axe
```
There are limits to the automation that Lean uses here, however.
{anchorName allTools}`allTools` is a list of all three tools:
```anchor allTools
def allTools : List WoodSplittingTool := [
  WoodSplittingTool.axe,
  WoodSplittingTool.maul,
  WoodSplittingTool.froe
]
```
Evaluating it leads to an error:
```anchor evalAllTools
#eval allTools
```
```anchorError evalAllTools
could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  List WoodSplittingTool
```
This is because Lean attempts to use code from a built-in table to display a list, but this code demands that display code for {anchorName WoodSplittingTool}`WoodSplittingTool` already exists.
This error can be worked around by instructing Lean to generate this display code when a datatype is defined, instead of at the last moment as part of {anchorTerm evalAllTools}`#eval`, by adding {anchorTerm Firewood}`deriving Repr` to its definition:
```anchor Firewood
inductive Firewood where
  | birch
  | pine
  | beech
deriving Repr
```
Evaluating a list of {anchorName Firewood}`Firewood` succeeds:
```anchor allFirewood
def allFirewood : List Firewood := [
  Firewood.birch,
  Firewood.pine,
  Firewood.beech
]
```
```anchor evalAllFirewood
#eval allFirewood
```
```anchorInfo evalAllFirewood
[Firewood.birch, Firewood.pine, Firewood.beech]
```
:::

# Exercises
%%%
tag := "polymorphism-exercises"
%%%

 * Write a function to find the last entry in a list. It should return an {anchorName fragments}`Option`.
 * Write a function that finds the first entry in a list that satisfies a given predicate. Start the definition with {anchorTerm List.findFirst?Ex}`def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := …`.
 * Write a function {anchorName Prod.switchEx}`Prod.switch` that switches the two fields in a pair for each other. Start the definition with {anchor Prod.switchEx}`def Prod.switch {α β : Type} (pair : α × β) : β × α := …`.
 * Rewrite the {anchorName PetName}`PetName` example to use a custom datatype and compare it to the version that uses {anchorName Sum}`Sum`.
 * Write a function {anchorName zipEx}`zip` that combines two lists into a list of pairs. The resulting list should be as long as the shortest input list. Start the definition with {anchor zipEx}`def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := …`.
 * Write a polymorphic function {anchorName takeOne}`take` that returns the first $`n` entries in a list, where $`n` is a {anchorName fragments}`Nat`. If the list contains fewer than $`n` entries, then the resulting list should be the entire input list. {anchorTerm takeThree}`#eval take 3 ["bolete", "oyster"]` should yield {anchorInfo takeThree}`["bolete", "oyster"]`, and {anchor takeOne}`#eval take 1 ["bolete", "oyster"]` should yield {anchorInfo takeOne}`["bolete"]`.
 * Using the analogy between types and arithmetic, write a function that distributes products over sums. In other words, it should have type {anchorTerm distr}`α × (β ⊕ γ) → (α × β) ⊕ (α × γ)`.
 * Using the analogy between types and arithmetic, write a function that turns multiplication by two into a sum. In other words, it should have type {anchorTerm distr}`Bool × α → α ⊕ α`.
