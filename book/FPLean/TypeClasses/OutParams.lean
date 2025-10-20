import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Controlling Instance Search" =>
%%%
tag := "out-params"
%%%

An instance of the {moduleName}`Add` class is sufficient to allow two expressions with type {moduleName}`Pos` to be conveniently added, producing another {moduleName}`Pos`.
However, in many cases, it can be useful to be more flexible and allow _heterogeneous_ operator overloading, where the arguments may have different types.
For example, adding a {moduleName}`Nat` to a {moduleName}`Pos` or a {moduleName}`Pos` to a {moduleName}`Nat` will always yield a {moduleName}`Pos`:

```anchor addNatPos
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)
```
These functions allow natural numbers to be added to positive numbers, but they cannot be used with the {moduleName}`Add` type class, which expects both arguments to {moduleName}`add` to have the same type.

# Heterogeneous Overloadings
%%%
tag := "heterogeneous-operators"
%%%

As mentioned in the section on {ref "overloaded-addition"}[overloaded addition], Lean provides a type class called {anchorName chapterIntro}`HAdd` for overloading addition heterogeneously.
The {anchorName chapterIntro}`HAdd` class takes three type parameters: the two argument types and the return type.
Instances of {anchorTerm haddInsts}`HAdd Nat Pos Pos` and {anchorTerm haddInsts}`HAdd Pos Nat Pos` allow ordinary addition notation to be used to mix the types:

```anchor haddInsts
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
```
Given the above two instances, the following examples work:
```anchor posNatEx
#eval (3 : Pos) + (5 : Nat)
```
```anchorInfo posNatEx
8
```
```anchor natPosEx
#eval (3 : Nat) + (5 : Pos)
```
```anchorInfo natPosEx
8
```

:::paragraph
The definition of the {anchorName chapterIntro}`HAdd` type class is very much like the following definition of {moduleName}`HPlus` with the corresponding instances:

```anchor HPlus
class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ
```

```anchor HPlusInstances
instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat
```
However, instances of {moduleName}`HPlus` are significantly less useful than instances of {anchorName chapterIntro}`HAdd`.
When attempting to use these instances with {kw}`#eval`, an error occurs:
```anchor hPlusOops
#eval toString (HPlus.hPlus (3 : Pos) (5 : Nat))
```
```anchorError hPlusOops
typeclass instance problem is stuck, it is often due to metavariables
  ToString ?m.14563
```
This happens because there is a metavariable in the type, and Lean has no way to solve it.
:::

As discussed in {ref "polymorphism"}[the initial description of polymorphism], metavariables represent unknown parts of a program that could not be inferred.
When an expression is written following {kw}`#eval`, Lean attempts to determine its type automatically.
In this case, it could not.
Because the third type parameter for {anchorName HPlusInstances}`HPlus` was unknown, Lean couldn't carry out type class instance search, but instance search is the only way that Lean could determine the expression's type.
That is, the {anchorTerm HPlusInstances}`HPlus Pos Nat Pos` instance can only apply if the expression should have type {moduleName}`Pos`, but there's nothing in the program other than the instance itself to indicate that it should have this type.

One solution to the problem is to ensure that all three types are available by adding a type annotation to the whole expression:
```anchor hPlusLotsaTypes
#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)
```
```anchorInfo hPlusLotsaTypes
8
```
However, this solution is not very convenient for users of the positive number library.


# Output Parameters
%%%
tag := "output-parameters"
%%%

This problem can also be solved by declaring {anchorName HPlus}`γ` to be an _output parameter_.
Most type class parameters are inputs to the search algorithm: they are used to select an instance.
For example, in an {moduleName}`OfNat` instance, both the type and the natural number are used to select a particular interpretation of a natural number literal.
However, in some cases, it can be convenient to start the search process even when some of the type parameters are not yet known, and use the instances that are discovered in the search to determine values for metavariables.
The parameters that aren't needed to start instance search are outputs of the process, which is declared with the {moduleName}`outParam` modifier:

```anchor HPlusOut
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ
```

With this output parameter, type class instance search is able to select an instance without knowing {anchorName HPlusOut}`γ` in advance.
For instance:
```anchor hPlusWorks
#eval HPlus.hPlus (3 : Pos) (5 : Nat)
```
```anchorInfo hPlusWorks
8
```

It might be helpful to think of output parameters as defining a kind of function.
Any given instance of a type class that has one or more output parameters provides Lean with instructions for determining the outputs from the inputs.
The process of searching for an instance, possibly recursively, ends up being more powerful than mere overloading.
Output parameters can determine other types in the program, and instance search can assemble a collection of underlying instances into a program that has this type.

# Default Instances
%%%
tag := "default-instances"
%%%

Deciding whether a parameter is an input or an output controls the circumstances under which Lean will initiate type class search.
In particular, type class search does not occur until all inputs are known.
However, in some cases, output parameters are not enough, and instance search should also occur when some inputs are unknown.
This is a bit like default values for optional function arguments in Python or Kotlin, except default _types_ are being selected.

_Default instances_ are instances that are available for instance search _even when not all their inputs are known_.
When one of these instances can be used, it will be used.
This can cause programs to successfully type check, rather than failing with errors related to unknown types and metavariables.
On the other hand, default instances can make instance selection less predictable.
In particular, if an undesired default instance is selected, then an expression may have a different type than expected, which can cause confusing type errors to occur elsewhere in the program.
Be selective about where default instances are used!

One example of where default instances can be useful is an instance of {anchorName HPlusOut}`HPlus` that can be derived from an {moduleName}`Add` instance.
In other words, ordinary addition is a special case of heterogeneous addition in which all three types happen to be the same.
This can be implemented using the following instance:

```anchor notDefaultAdd
instance [Add α] : HPlus α α α where
  hPlus := Add.add
```
With this instance, {anchorName notDefaultAdd}`hPlus` can be used for any addable type, like {moduleName}`Nat`:
```anchor hPlusNatNat
#eval HPlus.hPlus (3 : Nat) (5 : Nat)
```
```anchorInfo hPlusNatNat
8
```

However, this instance will only be used in situations where the types of both arguments are known.
For example,
```anchor plusFiveThree
#check HPlus.hPlus (5 : Nat) (3 : Nat)
```
yields the type
```anchorInfo plusFiveThree
HPlus.hPlus 5 3 : Nat
```
as expected, but
```anchor plusFiveMeta
#check HPlus.hPlus (5 : Nat)
```
yields a type that contains two metavariables, one for the remaining argument and one for the return type:
```anchorInfo plusFiveMeta
HPlus.hPlus 5 : ?m.15752 → ?m.15754
```

In the vast majority of cases, when someone supplies one argument to addition, the other argument will have the same type.
To make this instance into a default instance, apply the {anchorTerm defaultAdd}`default_instance` attribute:

```anchor defaultAdd
@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add
```
With this default instance, the example has a more useful type:
```anchor plusFive
#check HPlus.hPlus (5 : Nat)
```
yields
```anchorInfo plusFive
HPlus.hPlus 5 : Nat → Nat
```

Each operator that exists in overloadable heterogeneous and homogeneous versions follows the pattern of a default instance that allows the homogeneous version to be used in contexts where the heterogeneous is expected.
The infix operator is replaced with a call to the heterogeneous version, and the homogeneous default instance is selected when possible.

Similarly, simply writing {anchorTerm fiveType}`5` gives a {anchorTerm fiveType}`Nat` rather than a type with a metavariable that is waiting for more information in order to select an {moduleName}`OfNat` instance.
This is because the {moduleName}`OfNat` instance for {moduleName}`Nat` is a default instance.

Default instances can also be assigned _priorities_ that affect which will be chosen in situations where more than one might apply.
For more information on default instance priorities, please consult the Lean manual.


# Exercises
%%%
tag := "out-params-exercises"
%%%

Define an instance of {anchorTerm MulPPoint}`HMul (PPoint α) α (PPoint α)` that multiplies both projections by the scalar.
It should work for any type {anchorName MulPPoint}`α` for which there is a {anchorTerm MulPPoint}`Mul α` instance.
For example,
```anchor HMulPPoint
#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
```
should yield
```anchorInfo HMulPPoint
{ x := 5.000000, y := 7.400000 }
```
