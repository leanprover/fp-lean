import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true


#doc (Manual) "Additional Conveniences" =>
%%%
tag := "type-class-conveniences"
%%%

# Constructor Syntax for Instances
%%%
tag := "instance-constructor-syntax"
%%%

Behind the scenes, type classes are structure types and instances are values of these types.
The only differences are that Lean stores additional information about type classes, such as which parameters are output parameters, and that instances are registered for searching.
While values that have structure types are typically defined using either {lit}`⟨...⟩` syntax or with braces and fields, and instances are typically defined using {kw}`where`, both syntaxes work for both kinds of definition.

:::paragraph
For example, a forestry application might represent trees as follows:

```anchor trees
structure Tree : Type where
  latinName : String
  commonNames : List String

def oak : Tree :=
  ⟨"Quercus robur", ["common oak", "European oak"]⟩

def birch : Tree :=
  { latinName := "Betula pendula",
    commonNames := ["silver birch", "warty birch"]
  }

def sloe : Tree where
  latinName := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]
```
All three syntaxes are equivalent.
:::

:::paragraph
Similarly, type class instances can be defined using all three syntaxes:

```anchor Display
class Display (α : Type) where
  displayName : α → String

instance : Display Tree :=
  ⟨Tree.latinName⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

instance : Display Tree where
  displayName t := t.latinName
```

The {kw}`where` syntax is typically used for instances, while structures use either the curly-brace syntax or the {kw}`where` syntax.
The {lit}`⟨...⟩` syntax can be useful when emphasizing that a structure type is very much like a tuple in which the fields happen to be named, but the names are not important at the moment.
However, there are situations where it can make sense to use other alternatives.
In particular, a library might provide a function that constructs an instance value.
Placing a call to this function after {lit}`:=` in an instance declaration is the easiest way to use such a function.
:::

# Examples
%%%
tag := "example-command"
%%%

When experimenting with Lean code, definitions can be more convenient to use than {kw}`#eval` or {kw}`#check` commands.
First off, definitions don't produce any output, which can help keep the reader's focus on the most interesting output.
Secondly, it's easiest to write most Lean programs by starting with a type signature, allowing Lean to provide more assistance and better error messages while writing the program itself.
On the other hand, {kw}`#eval` and {kw}`#check` are easiest to use in contexts where Lean is able to determine the type from the provided expression.
Thirdly, {kw}`#eval` cannot be used with expressions whose types don't have {moduleName}`ToString` or {moduleName}`Repr` instances, such as functions.
Finally, multi-step {kw}`do` blocks, {kw}`let`-expressions, and other syntactic forms that take multiple lines are particularly difficult to write with a type annotation in {kw}`#eval` or {kw}`#check`, simply because the required parenthesization can be difficult to predict.

:::paragraph
To work around these issues, Lean supports the explicit indication of examples in a source file.
An example is like a definition without a name.
For instance, a non-empty list of birds commonly found in Copenhagen's green spaces can be written:

```anchor birdExample
example : NonEmptyList String :=
  { head := "Sparrow",
    tail := ["Duck", "Swan", "Magpie", "Eurasian coot", "Crow"]
  }
```
:::

:::paragraph
Examples may define functions by accepting arguments:

```anchor commAdd
example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n
```
While this creates a function behind the scenes, this function has no name and cannot be called.
Nonetheless, this is useful for demonstrating how a library can be used with arbitrary or unknown values of some given type.
In source files, {kw}`example` declarations are best paired with comments that explain how the example illustrates the concepts of the library.
:::
