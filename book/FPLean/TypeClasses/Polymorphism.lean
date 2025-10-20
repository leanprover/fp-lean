import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true



#doc (Manual) "Type Classes and Polymorphism" =>
%%%
tag := "tc-polymorphism"
%%%

It can be useful to write functions that work for _any_ overloading of a given function.
For example, {anchorTerm printlnType}`IO.println` works for any type that has an instance of {anchorTerm printlnType}`ToString`.
This is indicated using square brackets around the required instance: the type of {anchorTerm printlnType}`IO.println` is {anchorTerm printlnType}`{α : Type} → [ToString α] → α → IO Unit`.
This type says that {anchorTerm printlnType}`IO.println` accepts an argument of type {anchorTerm printlnType}`α`, which Lean should determine automatically, and that there must be a {anchorTerm printlnType}`ToString` instance available for {anchorTerm printlnType}`α`.
It returns an {anchorTerm printlnType}`IO` action.


# Checking Polymorphic Functions' Types
%%%
tag := "checking-polymorphic-types"
%%%

Checking the type of a function that takes implicit arguments or uses type classes requires the use of some additional syntax.
Simply writing
```anchor printlnMetas
#check (IO.println)
```
yields a type with metavariables:
```anchorInfo printlnMetas
IO.println : ?m.2620 → IO Unit
```
This is because Lean does its best to discover implicit arguments, and the presence of metavariables indicates that it did not yet discover enough type information to do so.
To understand the signature of a function, this feature can be suppressed with an at-sign ({anchorTerm printlnNoMetas}`@`) before the function's name:
```anchor printlnNoMetas
#check @IO.println
```
```anchorInfo printlnNoMetas
@IO.println : {α : Type u_1} → [ToString α] → α → IO Unit
```
There is a {lit}`u_1` after {lit}`Type`, which uses a feature of Lean that has not yet been introduced.
For now, ignore these parameters to {lit}`Type`.

# Defining Polymorphic Functions with Instance Implicits
%%%
tag := "defining-polymorphic-functions-with-instance-implicits"
%%%

:::paragraph
A function that sums all entries in a list needs two instances: {moduleName}`Add` allows the entries to be added, and an {moduleName}`OfNat` instance for {anchorTerm ListSum}`0` provides a sensible value to return for the empty list:

```anchor ListSum
def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
```
This function can be also defined with a {anchorTerm ListSumZ}`Zero α` requirement instead of {anchorTerm ListSum}`OfNat α 0`.
Both are equivalent, but {anchorTerm ListSumZ}`Zero α` can be easier to read:

```anchor ListSumZ
def List.sumOfContents [Add α] [Zero α] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
```
:::

:::paragraph

This function can be used for a list of {anchorTerm fourNats}`Nat`s:

```anchor fourNats
def fourNats : List Nat := [1, 2, 3, 4]
```
```anchor fourNatsSum
#eval fourNats.sumOfContents
```
```anchorInfo fourNatsSum
10
```
but not for a list of {anchorTerm fourPos}`Pos` numbers:

```anchor fourPos
def fourPos : List Pos := [1, 2, 3, 4]
```
```anchor fourPosSum
#eval fourPos.sumOfContents
```
```anchorError fourPosSum
failed to synthesize
  Zero Pos

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
The Lean standard library includes this function, where it is called {moduleName}`List.sum`.

:::

Specifications of required instances in square brackets are called _instance implicits_.
Behind the scenes, every type class defines a structure that has a field for each overloaded operation.
Instances are values of that structure type, with each field containing an implementation.
At a call site, Lean is responsible for finding an instance value to pass for each instance implicit argument.
The most important difference between ordinary implicit arguments and instance implicits is the strategy that Lean uses to find an argument value.
In the case of ordinary implicit arguments, Lean uses a technique called _unification_ to find a single unique argument value that would allow the program to pass the type checker.
This process relies only on the specific types involved in the function's definition and the call site.
For instance implicits, Lean instead consults a built-in table of instance values.

Just as the {anchorTerm OfNatPos}`OfNat` instance for {anchorName OfNatPos}`Pos` took a natural number {anchorName OfNatPos}`n` as an automatic implicit argument, instances may also take instance implicit arguments themselves.
The {ref "polymorphism"}[section on polymorphism] presented a polymorphic point type:

```anchor PPoint
structure PPoint (α : Type) where
  x : α
  y : α
```
Addition of points should add the underlying {anchorName PPoint}`x` and {anchorName PPoint}`y` fields.
Thus, an {anchorName AddPPoint}`Add` instance for {anchorName AddPPoint}`PPoint` requires an {anchorName AddPPoint}`Add` instance for whatever type these fields have.
In other words, the {anchorName AddPPoint}`Add` instance for {anchorName AddPPoint}`PPoint` requires a further {anchorName AddPPoint}`Add` instance for {anchorName AddPPoint}`α`:

```anchor AddPPoint
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }
```
When Lean encounters an addition of two points, it searches for and finds this instance.
It then performs a further search for the {anchorTerm AddPPoint}`Add α` instance.

The instance values that are constructed in this way are values of the type class's structure type.
A successful recursive instance search results in a structure value that has a reference to another structure value.
An instance of {anchorTerm AddPPointNat}`Add (PPoint Nat)` contains a reference to the instance of {anchorTerm AddPPointNat}`Add Nat` that was found.

This recursive search process means that type classes offer significantly more power than plain overloaded functions.
A library of polymorphic instances is a set of code building blocks that the compiler will assemble on its own, given nothing but the desired type.
Polymorphic functions that take instance arguments are latent requests to the type class mechanism to assemble helper functions behind the scenes.
The API's clients are freed from the burden of plumbing together all of the necessary parts by hand.


# Methods and Implicit Arguments
%%%
tag := "method-implicit-params"
%%%

The type of {anchorTerm ofNatType}`OfNat.ofNat` may be surprising.
It is {anchorTerm ofNatType}`: {α : Type} → (n : Nat) → [OfNat α n] → α`, in which the {anchorTerm ofNatType}`Nat` argument {anchorTerm ofNatType}`n` occurs as an explicit function parameter.
In the declaration of the method, however, {anchorName OfNat}`ofNat` simply has type {anchorName ofNatType}`α`.
This seeming discrepancy is because declaring a type class really results in the following:

 * A structure type to contain the implementation of each overloaded operation
 * A namespace with the same name as the class
 * For each method, a function in the class's namespace that retrieves its implementation from an instance

This is analogous to the way that declaring a new structure also declares accessor functions.
The primary difference is that a structure's accessors take the structure value as an explicit parameter, while the type class methods take the instance value as an instance implicit to be found automatically by Lean.

In order for Lean to find an instance, its parameters must be available.
This means that each parameter to the type class must be a parameter to the method that occurs before the instance.
It is most convenient when these parameters are implicit, because Lean does the work of discovering their values.
For example, {anchorTerm addType}`Add.add` has the type {anchorTerm addType}`{α : Type} → [Add α] → α → α → α`.
In this case, the type parameter {anchorTerm addType}`α` can be implicit because the arguments to {anchorTerm addType}`Add.add` provide information about which type the user intended.
This type can then be used to search for the {anchorTerm addType}`Add` instance.

In the case of {anchorName ofNatType}`OfNat.ofNat`, however, the particular {moduleName}`Nat` literal to be decoded does not appear as part of any other parameter's type.
This means that Lean would have no information to use when attempting to figure out the implicit parameter {anchorName ofNatType}`n`.
The result would be a very inconvenient API.
Thus, in these cases, Lean uses an explicit parameter for the class's method.



# Exercises
%%%
tag := "type-class-polymorphism-exercises"
%%%

## Even Number Literals
%%%
tag := none
%%%


Write an instance of {anchorName ofNatType}`OfNat` for the even number datatype from the {ref "even-numbers-ex"}[previous section's exercises] that uses recursive instance search.

## Recursive Instance Search Depth
%%%
tag := none
%%%

There is a limit to how many times the Lean compiler will attempt a recursive instance search.
This places a limit on the size of even number literals defined in the previous exercise.
Experimentally determine what the limit is.
