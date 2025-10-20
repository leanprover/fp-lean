import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "Additional Conveniences" =>
%%%
tag := "getting-to-know-conveniences"
%%%

Lean contains a number of convenience features that make programs much more concise.

# Automatic Implicit Parameters
%%%
tag := "automatic-implicit-parameters"
%%%

:::paragraph
When writing polymorphic functions in Lean, it is typically not necessary to list all the implicit parameters.
Instead, they can simply be mentioned.
If Lean can determine their type, then they are automatically inserted as implicit parameters.
In other words, the previous definition of {anchorName lengthImp}`length`:

```anchor lengthImp
def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

can be written without {anchorTerm lengthImp}`{α : Type}`:

```anchor lengthImpAuto
def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

This can greatly simplify highly polymorphic definitions that take many implicit parameters.

:::

# Pattern-Matching Definitions
%%%
tag := "pattern-matching-definitions"
%%%

When defining functions with {kw}`def`, it is quite common to name an argument and then immediately use it with pattern matching.
For instance, in {anchorName lengthImpAuto}`length`, the argument {anchorName lengthImpAuto}`xs` is used only in {kw}`match`.
In these situations, the cases of the {kw}`match` expression can be written directly, without naming the argument at all.

:::paragraph
The first step is to move the arguments' types to the right of the colon, so the return type is a function type.
For instance, the type of {anchorName lengthMatchDef}`length` is {anchorTerm lengthMatchDef}`List α → Nat`.
Then, replace the {lit}`:=` with each case of the pattern match:

```anchor lengthMatchDef
def length : List α → Nat
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

This syntax can also be used to define functions that take more than one argument.
In this case, their patterns are separated by commas.
For instance, {anchorName drop}`drop` takes a number $`n` and a list, and returns the list after removing the first $`n` entries.

```anchor drop
def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, x :: xs => drop n xs
```

:::

:::paragraph

Named arguments and patterns can also be used in the same definition.
For instance, a function that takes a default value and an optional value, and returns the default when the optional value is {anchorName fromOption}`none`, can be written:

```anchor fromOption
def fromOption (default : α) : Option α → α
  | none => default
  | some x => x
```

This function is called {anchorTerm fragments}`Option.getD` in the standard library, and can be called with dot notation:

```anchor getD
#eval (some "salmonberry").getD ""
```


```anchorInfo getD
"salmonberry"
```


```anchor getDNone
#eval none.getD ""
```


```anchorInfo getDNone
""
```

:::

# Local Definitions
%%%
tag := "local-definitions"
%%%

It is often useful to name intermediate steps in a computation.
In many cases, intermediate values represent useful concepts all on their own, and naming them explicitly can make the program easier to read.
In other cases, the intermediate value is used more than once.
As in most other languages, writing down the same code twice in Lean causes it to be computed twice, while saving the result in a variable leads to the result of the computation being saved and re-used.

:::paragraph

For instance, {anchorName unzipBad}`unzip` is a function that transforms a list of pairs into a pair of lists.
When the list of pairs is empty, then the result of {anchorName unzipBad}`unzip` is a pair of empty lists.
When the list of pairs has a pair at its head, then the two fields of the pair are added to the result of unzipping the rest of the list.
This definition of {anchorName unzipBad}`unzip` follows that description exactly:

```anchor unzipBad
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    (x :: (unzip xys).fst, y :: (unzip xys).snd)
```

Unfortunately, there is a problem: this code is slower than it needs to be.
Each entry in the list of pairs leads to two recursive calls, which makes this function take exponential time.
However, both recursive calls will have the same result, so there is no reason to make the recursive call twice.
:::

:::paragraph
In Lean, the result of the recursive call can be named, and thus saved, using {kw}`let`.
Local definitions with {kw}`let` resemble top-level definitions with {kw}`def`: it takes a name to be locally defined, arguments if desired, a type signature, and then a body following {lit}`:=`.
After the local definition, the expression in which the local definition is available (called the _body_ of the {kw}`let`-expression) must be on a new line, starting at a column in the file that is less than or equal to that of the {kw}`let` keyword.
A local definition with {kw}`let` in {anchorName unzip}`unzip` looks like this:

```anchor unzip
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

To use {kw}`let` on a single line, separate the local definition from the body with a semicolon.
:::

:::paragraph
Local definitions with {kw}`let` may also use pattern matching when one pattern is enough to match all cases of a datatype.
In the case of {anchorName unzip}`unzip`, the result of the recursive call is a pair.
Because pairs have only a single constructor, the name {anchorName unzip}`unzipped` can be replaced with a pair pattern:

```anchor unzipPat
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := unzip xys
    (x :: xs, y :: ys)
```

Judicious use of patterns with {kw}`let` can make code easier to read, compared to writing the accessor calls by hand.
:::

:::paragraph
The biggest difference between {kw}`let` and {kw}`def` is that recursive {kw}`let` definitions must be explicitly indicated by writing {kw}`let rec`.
For instance, one way to reverse a list involves a recursive helper function, as in this definition:

```anchor reverse
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []
```

The helper function walks down the input list, moving one entry at a time over to {anchorName reverse}`soFar`.
When it reaches the end of the input list, {anchorName reverse}`soFar` contains a reversed version of the input.
:::

# Type Inference
%%%
tag := "type-inference"
%%%

:::paragraph
In many situations, Lean can automatically determine an expression's type.
In these cases, explicit types may be omitted from both top-level definitions (with {kw}`def`) and local definitions (with {kw}`let`).
For example, the recursive call to {anchorName unzipNT}`unzip` does not need an annotation:

```anchor unzipNT
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

:::

As a rule of thumb, omitting the types of literal values (like strings and numbers) usually works, although Lean may pick a type for literal numbers that is more specific than the intended type.
Lean can usually determine a type for a function application, because it already knows the argument types and the return type.
Omitting return types for function definitions will often work, but function parameters typically require annotations.
Definitions that are not functions, like {anchorName unzipNT}`unzipped` in the example, do not need type annotations if their bodies do not need type annotations, and the body of this definition is a function application.

:::paragraph
Omitting the return type for {anchorName unzipNRT}`unzip` is possible when using an explicit {kw}`match` expression:

```anchor unzipNRT
def unzip (pairs : List (α × β)) :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

:::

:::paragraph

Generally speaking, it is a good idea to err on the side of too many, rather than too few, type annotations.
First off, explicit types communicate assumptions about the code to readers.
Even if Lean can determine the type on its own, it can still be easier to read code without having to repeatedly query Lean for type information.
Secondly, explicit types help localize errors.
The more explicit a program is about its types, the more informative the error messages can be.
This is especially important in a language like Lean that has a very expressive type system.
Thirdly, explicit types make it easier to write the program in the first place.
The type is a specification, and the compiler's feedback can be a helpful tool in writing a program that meets the specification.
Finally, Lean's type inference is a best-effort system.
Because Lean's type system is so expressive, there is no “best” or most general type to find for all expressions.
This means that even if you get a type, there's no guarantee that it's the _right_ type for a given application.
For instance, {anchorTerm fourteenNat}`14` can be a {anchorName length1}`Nat` or an {anchorName fourteenInt}`Int`:

```anchor fourteenNat
#check 14
```


```anchorInfo fourteenNat
14 : Nat
```


```anchor fourteenInt
#check (14 : Int)
```

```anchorInfo fourteenInt
14 : Int
```

:::

:::paragraph
Missing type annotations can give confusing error messages.
Omitting all types from the definition of {anchorName unzipNoTypesAtAll}`unzip`:

```anchor unzipNoTypesAtAll
def unzip pairs :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

leads to a message about the {kw}`match` expression:

```anchorError unzipNoTypesAtAll
Invalid match expression: This pattern contains metavariables:
  []
```

This is because {kw}`match` needs to know the type of the value being inspected, but that type was not available.
A “metavariable” is an unknown part of a program, written {lit}`?m.XYZ` in error messages—they are described in the {ref "polymorphism"}[section on Polymorphism].
In this program, the type annotation on the argument is required.
:::

:::paragraph
Even some very simple programs require type annotations.
For instance, the identity function just returns whatever argument it is passed.
With argument and type annotations, it looks like this:

```anchor idA
def id (x : α) : α := x
```

Lean is capable of determining the return type on its own:

```anchor idB
def id (x : α) := x
```

Omitting the argument type, however, causes an error:

```anchor identNoTypes
def id x := x
```


```anchorError identNoTypes
Failed to infer type of binder `x`
```
:::

In general, messages that say something like “failed to infer” or that mention metavariables are often a sign that more type annotations are necessary.
Especially while still learning Lean, it is useful to provide most types explicitly.

# Simultaneous Matching
%%%
tag := "simultaneous-matching"
%%%

:::paragraph

Pattern-matching expressions, just like pattern-matching definitions, can match on multiple values at once.
Both the expressions to be inspected and the patterns that they match against are written with commas between them, similarly to the syntax used for definitions.
Here is a version of {anchorName dropMatch}`drop` that uses simultaneous matching:

```anchor dropMatch
def drop (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys => ys
  | _, [] => []
  | Nat.succ n , y :: ys => drop n ys
```

:::

:::paragraph

Simultaneous matching resembles matching on a pair, but there is an important difference.
Lean tracks the connection between the expression being matched and the patterns, and this information is used for purposes that include checking for termination and propagating static type information.
As a result, the version of {anchorName sameLengthPair}`sameLength` that matches a pair is rejected by the termination checker, because the connection between {anchorName sameLengthPair}`xs` and {anchorTerm sameLengthPair}`x :: xs'` is obscured by the intervening pair:

```anchor sameLengthPair
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _ => false
```

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
1) 1748:28-46  ?  ?
Please use `termination_by` to specify a decreasing measure.
```

Simultaneously matching both lists is accepted:

```anchor sameLengthOk2
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => sameLength xs' ys'
  | _, _ => false
```

:::

# Natural Number Patterns
%%%
tag := "natural-number-patterns"
%%%

:::paragraph

In the section on {ref "datatypes-and-patterns"}[datatypes and patterns], {anchorName even}`even` was defined like this:

```anchor even
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
```

Just as there is special syntax to make list patterns more readable than using {anchorName length1}`List.cons` and {anchorName length1}`List.nil` directly, natural numbers can be matched using literal numbers and {anchorTerm evenFancy}`+`.
For example, {anchorName evenFancy}`even` can also be defined like this:

```anchor evenFancy
def even : Nat → Bool
  | 0 => true
  | n + 1 => not (even n)
```

In this notation, the arguments to the {anchorTerm evenFancy}`+` pattern serve different roles.
Behind the scenes, the left argument ({anchorName evenFancy}`n` above) becomes an argument to some number of {anchorName even}`Nat.succ` patterns, and the right argument ({anchorTerm evenFancy}`1` above) determines how many {anchorName even}`Nat.succ`s to wrap around the pattern.
The explicit patterns in {anchorName explicitHalve}`halve`, which divides a {anchorName explicitHalve}`Nat` by two and drops the remainder:

```anchor explicitHalve
def halve : Nat → Nat
  | Nat.zero => 0
  | Nat.succ Nat.zero => 0
  | Nat.succ (Nat.succ n) => halve n + 1
```

can be replaced by numeric literals and {anchorTerm halve}`+`:

```anchor halve
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1
```

Behind the scenes, both definitions are completely equivalent.
Remember: {anchorTerm halve}`halve n + 1` is equivalent to {anchorTerm halveParens}`(halve n) + 1`, not {anchorTerm halveParens}`halve (n + 1)`.

:::

:::paragraph

When using this syntax, the second argument to {anchorTerm halveFlippedPat}`+` should always be a literal {anchorName halveFlippedPat}`Nat`.
Even though addition is commutative, flipping the arguments in a pattern can result in errors like the following:

```anchor halveFlippedPat
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 + n => halve n + 1
```

```anchorError halveFlippedPat
Invalid pattern(s): `n` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching:
  .(Nat.add 2 n)
```

This restriction enables Lean to transform all uses of the {anchorTerm halveFlippedPat}`+` notation in a pattern into uses of the underlying {anchorName even}`Nat.succ`, keeping the language simpler behind the scenes.

:::

# Anonymous Functions
%%%
tag := "anonymous-functions"
%%%

:::paragraph

Functions in Lean need not be defined at the top level.
As expressions, functions are produced with the {kw}`fun` syntax.
Function expressions begin with the keyword {kw}`fun`, followed by one or more parameters, which are separated from the return expression using {lit}`=>`.
For instance, a function that adds one to a number can be written:

```anchor incr
#check fun x => x + 1
```

```anchorInfo incr
fun x => x + 1 : Nat → Nat
```

Type annotations are written the same way as on {kw}`def`, using parentheses and colons:

```anchor incrInt
#check fun (x : Int) => x + 1
```


```anchorInfo incrInt
fun x => x + 1 : Int → Int
```

Similarly, implicit parameters may be written with curly braces:

```anchor identLambda
#check fun {α : Type} (x : α) => x
```

```anchorInfo identLambda
fun {α} x => x : {α : Type} → α → α
```

This style of anonymous function expression is often referred to as a _lambda expression_, because the typical notation used in mathematical descriptions of programming languages uses the Greek letter λ (lambda) where Lean has the keyword {kw}`fun`.
Even though Lean does permit {kw}`λ` to be used instead of {kw}`fun`, it is most common to write {kw}`fun`.

:::

:::paragraph

Anonymous functions also support the multiple-pattern style used in {kw}`def`.
For instance, a function that returns the predecessor of a natural number if it exists can be written:

```anchor predHuh
#check fun
  | 0 => none
  | n + 1 => some n
```


```anchorInfo predHuh
fun x =>
  match x with
  | 0 => none
  | n.succ => some n : Nat → Option Nat
```

Note that Lean's own description of the function has a named argument and a {kw}`match` expression.
Many of Lean's convenient syntactic shorthands are expanded to simpler syntax behind the scenes, and the abstraction sometimes leaks.

:::

:::paragraph

Definitions using {kw}`def` that take arguments may be rewritten as function expressions.
For instance, a function that doubles its argument can be written as follows:

```anchor doubleLambda
def double : Nat → Nat := fun
  | 0 => 0
  | k + 1 => double k + 2
```


When an anonymous function is very simple, like {anchorEvalStep incrSteps 0}`fun x => x + 1`, the syntax for creating the function can be fairly verbose.
In that particular example, six non-whitespace characters are used to introduce the function, and its body consists of only three non-whitespace characters.
For these simple cases, Lean provides a shorthand.
In an expression surrounded by parentheses, a centered dot character {anchorTerm incrSteps}`·` can stand for a parameter, and the expression inside the parentheses becomes the function's body.
That particular function can also be written {anchorEvalStep incrSteps 1}`(· + 1)`.
:::

:::paragraph

The centered dot always creates a function out of the _closest_ surrounding set of parentheses.
For instance, {anchorEvalStep funPair 0}`(· + 5, 3)` is a function that returns a pair of numbers, while {anchorEvalStep pairFun 0}`((· + 5), 3)` is a pair of a function and a number.
If multiple dots are used, then they become parameters from left to right:

```anchorEvalSteps twoDots
(· , ·) 1 2
===>
(1, ·) 2
===>
(1, 2)
```

Anonymous functions can be applied in precisely the same way as functions defined using {kw}`def` or {kw}`let`.
The command {anchor applyLambda}`#eval (fun x => x + x) 5` results in:

```anchorInfo applyLambda
10
```

while {anchor applyCdot}`#eval (· * 2) 5` results in:

```anchorInfo applyCdot
10
```

:::

# Namespaces
%%%
tag := "namespaces"
%%%

Each name in Lean occurs in a _namespace_, which is a collection of names.
Names are placed in namespaces using {lit}`.`, so {anchorName fragments}`List.map` is the name {anchorName fragments}`map` in the {lit}`List` namespace.
Names in different namespaces do not conflict with each other, even if they are otherwise identical.
This means that {anchorName fragments}`List.map` and {anchorName fragments}`Array.map` are different names.
Namespaces may be nested, so {lit}`Project.Frontend.User.loginTime` is the name {lit}`loginTime` in the nested namespace {lit}`Project.Frontend.User`.

:::paragraph
Names can be directly defined within a namespace.
For instance, the name {anchorName fragments}`double` can be defined in the {anchorName even}`Nat` namespace:

```anchor NatDouble
def Nat.double (x : Nat) : Nat := x + x
```

Because {anchorName even}`Nat` is also the name of a type, dot notation is available to call {anchorName fragments}`Nat.double` on expressions with type {anchorName even}`Nat`:

```anchor NatDoubleFour
#eval (4 : Nat).double
```

```anchorInfo NatDoubleFour
8
```

:::

:::paragraph

In addition to defining names directly in a namespace, a sequence of declarations can be placed in a namespace using the {kw}`namespace` and {kw}`end` commands.
For instance, this defines {anchorName NewNamespace}`triple` and {anchorName NewNamespace}`quadruple` in the namespace {lit}`NewNamespace`:

```anchor NewNamespace
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace
```

To refer to them, prefix their names with {lit}`NewNamespace.`:

```anchor tripleNamespace
#check NewNamespace.triple
```

```anchorInfo tripleNamespace
NewNamespace.triple (x : Nat) : Nat
```


```anchor quadrupleNamespace
#check NewNamespace.quadruple
```

```anchorInfo quadrupleNamespace
NewNamespace.quadruple (x : Nat) : Nat
```

:::

:::paragraph
Namespaces may be _opened_, which allows the names in them to be used without explicit qualification.
Writing {kw}`open` {lit}`MyNamespace `{kw}`in` before an expression causes the contents of {lit}`MyNamespace` to be available in the expression.
For example, {anchorName quadrupleOpenDef}`timesTwelve` uses both {anchorName quadrupleOpenDef}`quadruple` and {anchorName quadrupleOpenDef}`triple` after opening {anchorTerm NewNamespace}`NewNamespace`:

```anchor quadrupleOpenDef
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)
```

:::

:::paragraph
Namespaces can also be opened prior to a command.
This allows all parts of the command to refer to the contents of the namespace, rather than just a single expression.
To do this, place the {kw}`open`﻿{lit}` ... `{kw}`in` prior to the command.

```anchor quadrupleNamespaceOpen
open NewNamespace in
#check quadruple
```

```anchorInfo quadrupleNamespaceOpen
NewNamespace.quadruple (x : Nat) : Nat
```

Function signatures show the name's full namespace.
Namespaces may additionally be opened for _all_ following commands for the rest of the file.
To do this, simply omit the {kw}`in` from a top-level usage of {kw}`open`.

:::

# {lit}`if let`
%%%
tag := "if-let"
%%%

:::paragraph
When consuming values that have a sum type, it is often the case that only a single constructor is of interest.
For example, given this type that represents a subset of Markdown inline elements:

```anchor Inline
inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline
```

a function that recognizes string elements and extracts their contents can be written:

```anchor inlineStringHuhMatch
def Inline.string? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _ => none
```

:::

:::paragraph
An alternative way of writing this function's body uses {kw}`if` together with {kw}`let`:

```anchor inlineStringHuh
def Inline.string? (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none
```

This is very much like the pattern-matching {kw}`let` syntax.
The difference is that it can be used with sum types, because a fallback is provided in the {kw}`else` case.
In some contexts, using {kw}`if let` instead of {kw}`match` can make code easier to read.

:::

# Positional Structure Arguments
%%%
tag := "positional-structure-arguments"
%%%

The {ref "structures"}[section on structures] presents two ways of constructing structures:
 1. The constructor can be called directly, as in {anchorTerm pointCtor}`Point.mk 1 2`.
 2. Brace notation can be used, as in {anchorTerm pointBraces}`{ x := 1, y := 2 }`.

In some contexts, it can be convenient to pass arguments positionally, rather than by name, but without naming the constructor directly.
For instance, defining a variety of similar structure types can help keep domain concepts separate, but the natural way to read the code may treat each of them as being essentially a tuple.
In these contexts, the arguments can be enclosed in angle brackets {lit}`⟨` and {lit}`⟩`.
A {anchorName pointBraces}`Point` can be written {anchorTerm pointPos}`⟨1, 2⟩`.
Be careful!
Even though they look like the less-than sign {lit}`<` and greater-than sign {lit}`>`, these brackets are different.
They can be input using {lit}`\<` and {lit}`\>`, respectively.

:::paragraph
Just as with the brace notation for named constructor arguments, this positional syntax can only be used in a context where Lean can determine the structure's type, either from a type annotation or from other type information in the program.
For instance, {anchorTerm pointPosEvalNoType}`#eval ⟨1, 2⟩` yields the following error:

```anchorError pointPosEvalNoType
Invalid `⟨...⟩` notation: The expected type of this term could not be determined
```

This error occurs because there is no type information available.
Adding an annotation, such as in {anchorTerm pointPosWithType}`#eval (⟨1, 2⟩ : Point)`, solves the problem:

```anchorInfo pointPosWithType
{ x := 1.000000, y := 2.000000 }
```

:::

# String Interpolation
%%%
tag := "string-interpolation"
%%%

:::paragraph
In Lean, prefixing a string with {kw}`s!` triggers _interpolation_, where expressions contained in curly braces inside the string are replaced with their values.
This is similar to {python}`f`-strings in Python and {CSharp}`$`-prefixed strings in C#.
For instance,

```anchor interpolation
#eval s!"three fives is {NewNamespace.triple 5}"
```

yields the output

```anchorInfo interpolation
"three fives is 15"
```

:::

:::paragraph
Not all expressions can be interpolated into a string.
For instance, attempting to interpolate a function results in an error.

```anchor interpolationOops
#check s!"three fives is {NewNamespace.triple}"
```

yields the error

```anchorError interpolationOops
failed to synthesize
  ToString (Nat → Nat)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

This is because there is no standard way to convert functions into strings.
Just as the compiler maintains a table that describes how to display the result of evaluating expressions of various types, it maintains a table that describes how to convert values of various types into strings.
The message {lit}`failed to synthesize instance` means that the Lean compiler didn't find an entry in this table for the given type.
The chapter on {ref "type-classes"}[type classes] describes this mechanism in more detail, including the means of adding new entries to the table.
:::
