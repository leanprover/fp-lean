import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Conveniences"

#doc (Manual) "Additional Conveniences" =>
%%%
tag := "monads-conveniences"
%%%

# Shared Argument Types
%%%
tag := "shared-argument-types"
%%%

When defining a function that takes multiple arguments that have the same type, both can be written before the same colon.
For example,

```anchor equalHuhOld
def equal? [BEq α] (x : α) (y : α) : Option α :=
  if x == y then
    some x
  else
    none
```
can be written

```anchor equalHuhNew
def equal? [BEq α] (x y : α) : Option α :=
  if x == y then
    some x
  else
    none
```
This is especially useful when the type signature is large.

# Leading Dot Notation
%%%
tag := "leading-dot-notation"
%%%

The constructors of an inductive type are in a namespace.
This allows multiple related inductive types to use the same constructor names, but it can lead to programs becoming verbose.
In contexts where the inductive type in question is known, the namespace can be omitted by preceding the constructor's name with a dot, and Lean uses the expected type to resolve the constructor names.
For example, a function that mirrors a binary tree can be written:

```anchor mirrorOld
def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)
```
Omitting the namespaces makes it significantly shorter, at the cost of making the program harder to read in contexts like code review tools that don't include the Lean compiler:

```anchor mirrorNew
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
```

Using the expected type of an expression to disambiguate a namespace is also applicable to names other than constructors.
If {anchorName BinTreeEmpty}`BinTree.empty` is defined as an alternative way of creating {anchorName BinTreeEmpty}`BinTree`s, then it can also be used with dot notation:

```anchor BinTreeEmpty
def BinTree.empty : BinTree α := .leaf
```
```anchor emptyDot
#check (.empty : BinTree Nat)
```
```anchorInfo emptyDot
BinTree.empty : BinTree Nat
```

# Or-Patterns
%%%
tag := "or-patterns"
%%%

In contexts that allow multiple patterns, such as {kw}`match`-expressions, multiple patterns may share their result expressions.
The datatype {anchorName Weekday}`Weekday` that represents days of the week:

```anchor Weekday
inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr
```

Pattern matching can be used to check whether a day is a weekend:

```anchor isWeekendA
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | Weekday.saturday => true
  | Weekday.sunday => true
  | _ => false
```
This can already be simplified by using constructor dot notation:

```anchor isWeekendB
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday => true
  | .sunday => true
  | _ => false
```
Because both weekend patterns have the same result expression ({anchorName isWeekendC}`true`), they can be condensed into one:

```anchor isWeekendC
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday | .sunday => true
  | _ => false
```
This can be further simplified into a version in which the argument is not named:

```anchor isWeekendD
def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false
```

Behind the scenes, the result expression is simply duplicated across each pattern.
This means that patterns can bind variables, as in this example that removes the {anchorName SumNames}`inl` and {anchorName SumNames}`inr` constructors from a sum type in which both contain the same type of value:

```anchor condense
def condense : α ⊕ α → α
  | .inl x | .inr x => x
```
Because the result expression is duplicated, the variables bound by the patterns are not required to have the same types.
Overloaded functions that work for multiple types may be used to write a single result expression that works for patterns that bind variables of different types:

```anchor stringy
def stringy : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"It is {repr x}"
```
In practice, only variables shared in all patterns can be referred to in the result expression, because the result must make sense for each pattern.
In {anchorName getTheNat}`getTheNat`, only {anchorName getTheNat}`n` can be accessed, and attempts to use either {anchorName getTheNat}`x` or {anchorName getTheNat}`y` lead to errors.

```anchor getTheNat
def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, x) | .inr (n, y) => n
```
Attempting to access {anchorName getTheAlpha}`x` in a similar definition causes an error because there is no {anchorName getTheAlpha}`x` available in the second pattern:
```anchor getTheAlpha
def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
  | .inl (n, x) | .inr (n, y) => x
```
```anchorError getTheAlpha
Unknown identifier `x`
```

The fact that the result expression is essentially copy-pasted to each branch of the pattern match can lead to some surprising behavior.
For example, the following definitions are acceptable because the {anchorName SumNames}`inr` version of the result expression refers to the global definition of {anchorName getTheString}`str`:

```anchor getTheString
def str := "Some string"

def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (n, str) | .inr (n, y) => str
```
Calling this function on both constructors reveals the confusing behavior.
In the first case, a type annotation is needed to tell Lean which type {anchorName getTheString}`β` should be:
```anchor getOne
#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String))
```
```anchorInfo getOne
"twenty"
```
In the second case, the global definition is used:
```anchor getTwo
#eval getTheString (.inr (20, "twenty"))
```
```anchorInfo getTwo
"Some string"
```

Using or-patterns can vastly simplify some definitions and increase their clarity, as in {anchorName isWeekendD}`Weekday.isWeekend`.
Because there is a potential for confusing behavior, it's a good idea to be careful when using them, especially when variables of multiple types or disjoint sets of variables are involved.
