import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Coercions" =>
%%%
tag := "coercions"
%%%


In mathematics, it is common to use the same symbol to stand for different aspects of some object in different contexts.
For example, if a ring is referred to in a context where a set is expected, then it is understood that the ring's underlying set is what's intended.
In programming languages, it is common to have rules to automatically translate values of one type into values of another type.
Java allows a {java}`byte` to be automatically promoted to an {java}`int`, and Kotlin allows a non-nullable type to be used in a context that expects a nullable version of the type.

In Lean, both purposes are served by a mechanism called {deftech}_coercions_.
When Lean encounters an expression of one type in a context that expects a different type, it will attempt to coerce the expression before reporting a type error.
Unlike Java, C, and Kotlin, the coercions are extensible by defining instances of type classes.

# Strings and Paths
%%%
tag := "string-path-coercion"
%%%

In the {ref "handling-input"}[source code to {lit}`feline`], a {moduleName}`String` is converted to a {moduleName}`FilePath` using the anonymous constructor syntax.
In fact, this was not necessary: Lean defines a coercion from {moduleName}`String` to {moduleName}`FilePath`, so a string can be used in an position where a path is expected.
Even though the function {anchorTerm readFile}`IO.FS.readFile` has type {anchorTerm readFile}`System.FilePath → IO String`, the following code is accepted by Lean:

```anchor fileDumper
def fileDumper : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStr "Which file? "
  stdout.flush
  let f := (← stdin.getLine).trim
  stdout.putStrLn s!"'The file {f}' contains:"
  stdout.putStrLn (← IO.FS.readFile f)
```
{moduleName}`String.trim` removes leading and trailing whitespace from a string.
On the last line of {anchorName fileDumper}`fileDumper`, the coercion from {moduleName}`String` to {moduleName}`FilePath` automatically converts {anchorName fileDumper}`f`, so it is not necessary to write {lit}`IO.FS.readFile ⟨f⟩`.

# Positive Numbers
%%%
tag := "positive-number-coercion"
%%%

Every positive number corresponds to a natural number.
The function {anchorName posToNat}`Pos.toNat` that was defined earlier converts a {moduleName}`Pos` to the corresponding {moduleName}`Nat`:

```anchor posToNat
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
```
The function {anchorName drop}`List.drop`, with type {anchorTerm drop}`{α : Type} → Nat → List α → List α`, removes a prefix of a list.
Applying {anchorName drop}`List.drop` to a {moduleName}`Pos`, however, leads to a type error:
```anchorTerm dropPos
[1, 2, 3, 4].drop (2 : Pos)
```
```anchorError dropPos
Application type mismatch: The argument
  2
has type
  Pos
but is expected to have type
  Nat
in the application
  List.drop 2
```
Because the author of {anchorName drop}`List.drop` did not make it a method of a type class, it can't be overridden by defining a new instance.

:::paragraph
The type class {moduleName}`Coe` describes overloaded ways of coercing from one type to another:

```anchor Coe
class Coe (α : Type) (β : Type) where
  coe : α → β
```
An instance of {anchorTerm CoePosNat}`Coe Pos Nat` is enough to allow the prior code to work:

```anchor CoePosNat
instance : Coe Pos Nat where
  coe x := x.toNat
```
```anchor dropPosCoe
#eval [1, 2, 3, 4].drop (2 : Pos)
```
```anchorInfo dropPosCoe
[3, 4]
```
Using {kw}`#check` shows the result of the instance search that was used behind the scenes:
```anchor checkDropPosCoe
#check [1, 2, 3, 4].drop (2 : Pos)
```
```anchorInfo checkDropPosCoe
List.drop (Pos.toNat 2) [1, 2, 3, 4] : List Nat
```
:::

# Chaining Coercions
%%%
tag := "chaining-coercions"
%%%

When searching for coercions, Lean will attempt to assemble a coercion out of a chain of smaller coercions.
For example, there is already a coercion from {anchorName chapterIntro}`Nat` to {anchorName chapterIntro}`Int`.
Because of that instance, combined with the {anchorTerm CoePosNat}`Coe Pos Nat` instance, the following code is accepted:

```anchor posInt
def oneInt : Int := Pos.one
```
This definition uses two coercions: from {anchorTerm CoePosNat}`Pos` to {anchorTerm CoePosNat}`Nat`, and then from {anchorTerm CoePosNat}`Nat` to {anchorTerm chapterIntro}`Int`.

The Lean compiler does not get stuck in the presence of circular coercions.
For example, even if two types {anchorName CoercionCycle}`A` and {anchorName CoercionCycle}`B` can be coerced to one another, their mutual coercions can be used to find a path:

```anchor CoercionCycle
inductive A where
  | a

inductive B where
  | b

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := ()
```
Remember: the double parentheses {anchorTerm CoercionCycle}`()` is short for the constructor {anchorName chapterIntro}`Unit.unit`.
After deriving a {anchorTerm ReprBTm}`Repr B` instance with {anchorTerm ReprB}`deriving instance Repr for B`,
```anchor coercedToBEval
#eval coercedToB
```
results in:
```anchorInfo coercedToBEval
B.b
```

:::paragraph
The {anchorName CoeOption}`Option` type can be used similarly to nullable types in C# and Kotlin: the {anchorName NEListGetHuh}`none` constructor represents the absence of a value.
The Lean standard library defines a coercion from any type {anchorName CoeOption}`α` to {anchorTerm CoeOption}`Option α` that wraps the value in {anchorName CoeOption}`some`.
This allows option types to be used in a manner even more similar to nullable types, because {anchorName CoeOption}`some` can be omitted.
For instance, the function {anchorName lastHuh}`List.last?` that finds the last entry in a list can be written without a {anchorName CoeOption}`some` around the return value {anchorName lastHuh}`x`:

```anchor lastHuh
def List.last? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x :: xs)
```
Instance search finds the coercion, and inserts a call to {anchorName Coe}`coe`, which wraps the argument in {anchorName CoeOption}`some`.
These coercions can be chained, so that nested uses of {anchorName CoeOption}`Option` don't require nested {anchorName CoeOption}`some` constructors:

```anchor perhapsPerhapsPerhaps
def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"
```
:::

:::paragraph
Coercions are only activated automatically when Lean encounters a mismatch between an inferred type and a type that is imposed from the rest of the program.
In cases with other errors, coercions are not activated.
For example, if the error is that an instance is missing, coercions will not be used:
```anchor ofNatBeforeCoe
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  392
```
```anchorError ofNatBeforeCoe
failed to synthesize
  OfNat (Option (Option (Option Nat))) 392
numerals are polymorphic in Lean, but the numeral `392` cannot be used in a context where the expected type is
  Option (Option (Option Nat))
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::

:::paragraph
This can be worked around by manually indicating the desired type to be used for {moduleName}`OfNat`:

```anchor perhapsPerhapsPerhapsNat
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  (392 : Nat)
```
Additionally, coercions can be manually inserted using an up arrow:

```anchor perhapsPerhapsPerhapsNatUp
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  ↑(392 : Nat)
```
In some cases, this can be used to ensure that Lean finds the right instances.
It can also make the programmer's intentions more clear.
:::

# Non-Empty Lists and Dependent Coercions
%%%
tag := "CoeDep"
%%%

An instance of {anchorTerm chapterIntro}`Coe α β` makes sense when the type {anchorName chapterIntro}`β` has a value that can represent each value from the type {anchorName chapterIntro}`α`.
Coercing from {moduleName}`Nat` to {moduleName}`Int` makes sense, because the type {moduleName}`Int` contains all the natural numbers, but a coercion from {moduleName}`Int` to {moduleName}`Nat` is a poor idea because {moduleName}`Nat` does not contain the negative numbers.
Similarly, a coercion from non-empty lists to ordinary lists makes sense because the {moduleName}`List` type can represent every non-empty list:

```anchor CoeNEList
instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs
```
This allows non-empty lists to be used with the entire {moduleName}`List` API.

On the other hand, it is impossible to write an instance of {anchorTerm coeNope}`Coe (List α) (NonEmptyList α)`, because there's no non-empty list that can represent the empty list.
This limitation can be worked around by using another version of coercions, which are called _dependent coercions_.
Dependent coercions can be used when the ability to coerce from one type to another depends on which particular value is being coerced.
Just as the {anchorName OfNat}`OfNat` type class takes the particular {moduleName}`Nat` being overloaded as a parameter, dependent coercion takes the value being coerced as a parameter:

```anchor CoeDep
class CoeDep (α : Type) (x : α) (β : Type) where
  coe : β
```
This is a chance to select only certain values, either by imposing further type class constraints on the value or by writing certain constructors directly.
For example, any {moduleName}`List` that is not actually empty can be coerced to a {moduleName}`NonEmptyList`:

```anchor CoeDepListNEList
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }
```

# Coercing to Types
%%%
tag := "CoeSort"
%%%

In mathematics, it is common to have a concept that consists of a set equipped with additional structure.
For example, a monoid is some set $`S`, an element $`s` of $`S`, and an associative binary operator on $`S`, such that $`s` is neutral on the left and right of the operator.
$`S` is referred to as the “carrier set” of the monoid.
The natural numbers with zero and addition form a monoid, because addition is associative and adding zero to any number is the identity.
Similarly, the natural numbers with one and multiplication also form a monoid.
Monoids are also widely used in functional programming: lists, the empty list, and the append operator form a monoid, as do strings, the empty string, and string append:

```anchor Monoid
structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }
```
Given a monoid, it is possible to write the {anchorName firstFoldMap}`foldMap` function that, in a single pass, transforms the entries in a list into a monoid's carrier set and then combines them using the monoid's operator.
Because monoids have a neutral element, there is a natural result to return when the list is empty, and because the operator is associative, clients of the function don't have to care whether the recursive function combines elements from left to right or from right to left.

```anchor firstFoldMap
def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs
```

Even though a monoid consists of three separate pieces of information, it is common to just refer to the monoid's name in order to refer to its set.
Instead of saying “Let A be a monoid and let _x_ and _y_ be elements of its carrier set”, it is common to say “Let _A_ be a monoid and let _x_ and _y_ be elements of _A_”.
This practice can be encoded in Lean by defining a new kind of coercion, from the monoid to its carrier set.

The {anchorName CoeMonoid}`CoeSort` class is just like the {anchorName CoePosNat}`Coe` class, with the exception that the target of the coercion must be a _sort_, namely {anchorTerm chapterIntro}`Type` or {anchorTerm chapterIntro}`Prop`.
The term _sort_ in Lean refers to these types that classify other types—{anchorTerm Coe}`Type` classifies types that themselves classify data, and {anchorTerm chapterIntro}`Prop` classifies propositions that themselves classify evidence of their truth.
Just as {anchorName CoePosNat}`Coe` is checked when a type mismatch occurs, {anchorName CoeMonoid}`CoeSort` is used when something other than a sort is provided in a context where a sort would be expected.

The coercion from a monoid into its carrier set extracts the carrier:

```anchor CoeMonoid
instance : CoeSort Monoid Type where
  coe m := m.Carrier
```
With this coercion, the type signatures become less bureaucratic:

```anchor foldMap
def foldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs
```

Another useful example of {anchorName CoeMonoid}`CoeSort` is used to bridge the gap between {anchorName types}`Bool` and {anchorTerm chapterIntro}`Prop`.
As discussed in {ref "equality-and-ordering"}[the section on ordering and equality], Lean's {kw}`if` expression expects the condition to be a decidable proposition rather than a {anchorName types}`Bool`.
Programs typically need to be able to branch based on Boolean values, however.
Rather than have two kinds of {kw}`if` expression, the Lean standard library defines a coercion from {anchorName types}`Bool` to the proposition that the {anchorName types}`Bool` in question is equal to {anchorName types}`true`:

```anchor CoeBoolProp
instance : CoeSort Bool Prop where
  coe b := b = true
```
In this case, the sort in question is {anchorTerm chapterIntro}`Prop` rather than {anchorTerm chapterIntro}`Type`.

# Coercing to Functions
%%%
tag := "CoeFun"
%%%

Many datatypes that occur regularly in programming consist of a function along with some extra information about it.
For example, a function might be accompanied by a name to show in logs or by some configuration data.
Additionally, putting a type in a field of a structure, similarly to the {anchorName Monoid}`Monoid` example, can make sense in contexts where there is more than one way to implement an operation and more manual control is needed than type classes would allow.
For example, the specific details of values emitted by a JSON serializer may be important because another application expects a particular format.
Sometimes, the function itself may be derivable from just the configuration data.

A type class called {anchorName CoeFun}`CoeFun` can transform values from non-function types to function types.
{anchorName CoeFun}`CoeFun` has two parameters: the first is the type whose values should be transformed into functions, and the second is an output parameter that determines exactly which function type is being targeted.

```anchor CoeFun
class CoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
  coe : (x : α) → makeFunctionType x
```
The second parameter is itself a function that computes a type.
In Lean, types are first-class and can be passed to functions or returned from them, just like anything else.

For example, a function that adds a constant amount to its argument can be represented as a wrapper around the amount to add, rather than by defining an actual function:

```anchor Adder
structure Adder where
  howMuch : Nat
```
A function that adds five to its argument has a {anchorTerm add5}`5` in the {anchorName Adder}`howMuch` field:

```anchor add5
def add5 : Adder := ⟨5⟩
```
This {anchorName Adder}`Adder` type is not a function, and applying it to an argument results in an error:
```anchor add5notfun
#eval add5 3
```
```anchorError add5notfun
Function expected at
  add5
but this term has type
  Adder

Note: Expected a function because this term is being applied to the argument
  3
```
Defining a {anchorName CoeFunAdder}`CoeFun` instance causes Lean to transform the adder into a function with type {anchorTerm CoeFunAdder}`Nat → Nat`:

```anchor CoeFunAdder
instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)
```
```anchor add53
#eval add5 3
```
```anchorInfo add53
8
```
Because all {anchorName CoeFunAdder}`Adder`s should be transformed into {anchorTerm CoeFunAdder}`Nat → Nat` functions, the argument to {anchorName CoeFunAdder}`CoeFun`'s second parameter was ignored.

:::paragraph
When the value itself is needed to determine the right function type, then {anchorName CoeFunAdder}`CoeFun`'s second parameter is no longer ignored.
For example, given the following representation of JSON values:

```anchor JSON
inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON
```
a JSON serializer is a structure that tracks the type it knows how to serialize along with the serialization code itself:

```anchor Serializer
structure Serializer where
  Contents : Type
  serialize : Contents → JSON
```
A serializer for strings need only wrap the provided string in the {anchorName StrSer}`JSON.string` constructor:

```anchor StrSer
def Str : Serializer :=
  { Contents := String,
    serialize := JSON.string
  }
```
:::

:::paragraph
Viewing JSON serializers as functions that serialize their argument requires extracting the inner type of serializable data:

```anchor CoeFunSer
instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize
```
Given this instance, a serializer can be applied directly to an argument:

```anchor buildResponse
def buildResponse (title : String) (R : Serializer)
    (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]
```
The serializer can be passed directly to {anchorName buildResponseOut}`buildResponse`:
```anchor buildResponseOut
#eval buildResponse "Functional Programming in Lean" Str "Programming is fun!"
```
```anchorInfo buildResponseOut
JSON.object
  [("title", JSON.string "Functional Programming in Lean"),
   ("status", JSON.number 200.000000),
   ("record", JSON.string "Programming is fun!")]
```
:::

## Aside: JSON as a String
%%%
tag := "json-string"
%%%

It can be a bit difficult to understand JSON when encoded as Lean objects.
To help make sure that the serialized response was what was expected, it can be convenient to write a simple converter from {anchorName JSON}`JSON` to {anchorName dropDecimals}`String`.
The first step is to simplify the display of numbers.
{anchorName JSON}`JSON` doesn't distinguish between integers and floating point numbers, and the type {anchorName JSON}`Float` is used to represent both.
In Lean, {anchorName chapterIntro}`Float.toString` includes a number of trailing zeros:
```anchor fiveZeros
#eval (5 : Float).toString
```
```anchorInfo fiveZeros
"5.000000"
```
The solution is to write a little function that cleans up the presentation by dropping all trailing zeros, followed by a trailing decimal point:

```anchor dropDecimals
def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropRightWhile (· == '0')
    noTrailingZeros.dropRightWhile (· == '.')
  else numString
```
With this definition, {anchorTerm dropDecimalExample}`dropDecimals (5 : Float).toString` yields {anchorTerm dropDecimalExample}`5`, and {anchorTerm dropDecimalExample2}`dropDecimals (5.2 : Float).toString` yields {anchorTerm dropDecimalExample2}`5.2`.

The next step is to define a helper function to append a list of strings with a separator in between them:

```anchor Stringseparate
def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))
```
This function is useful to account for comma-separated elements in JSON arrays and objects.
{anchorTerm sep2ex}`", ".separate ["1", "2"]` yields {anchorInfo sep2ex}`"1, 2"`, {anchorTerm sep1ex}`", ".separate ["1"]` yields {anchorInfo sep1ex}`"1"`, and {anchorTerm sep0ex}`", ".separate []` yields {anchorInfo sep0ex}`""`.
In the Lean standard library, this function is called {anchorName chapterIntro}`String.intercalate`.

Finally, a string escaping procedure is needed for JSON strings, so that the Lean string containing {anchorTerm chapterIntro}`"Hello!"` can be output as {anchorTerm escapeQuotes}`"\"Hello!\""`.
Fortunately, the Lean compiler contains an internal function for escaping JSON strings already, called {anchorName escapeQuotes}`Lean.Json.escape`.
To access this function, add {lit}`import Lean` to the beginning of your file.

The function that emits a string from a {anchorName JSONasString}`JSON` value is declared {kw}`partial` because Lean cannot see that it terminates.
This is because recursive calls to {anchorName JSONasString}`asString` occur in functions that are being applied by {anchorName chapterIntro}`List.map`, and this pattern of recursion is complicated enough that Lean cannot see that the recursive calls are actually being performed on smaller values.
In an application that just needs to produce JSON strings and doesn't need to mathematically reason about the process, having the function be {kw}`partial` is not likely to cause problems.

```anchor JSONasString
partial def JSON.asString (val : JSON) : String :=
  match val with
  | true => "true"
  | false => "false"
  | null => "null"
  | string s => "\"" ++ Lean.Json.escape s ++ "\""
  | number n => dropDecimals n.toString
  | object members =>
    let memberToString mem :=
      "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | array elements =>
    "[" ++ ", ".separate (elements.map asString) ++ "]"
```
With this definition, the output of serialization is easier to read:
```anchor buildResponseStr
#eval (buildResponse "Functional Programming in Lean" Str "Programming is fun!").asString
```
```anchorInfo buildResponseStr
"{\"title\": \"Functional Programming in Lean\", \"status\": 200, \"record\": \"Programming is fun!\"}"
```


# Messages You May Meet
%%%
tag := "coercion-messages"
%%%

Natural number literals are overloaded with the {anchorName OfNat}`OfNat` type class.
Because coercions fire in cases where types don't match, rather than in cases of missing instances, a missing {anchorName OfNat}`OfNat` instance for a type does not cause a coercion from {moduleName}`Nat` to be applied:
```anchor ofNatBeforeCoe
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  392
```
```anchorError ofNatBeforeCoe
failed to synthesize
  OfNat (Option (Option (Option Nat))) 392
numerals are polymorphic in Lean, but the numeral `392` cannot be used in a context where the expected type is
  Option (Option (Option Nat))
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

# Design Considerations
%%%
tag := "coercion-design-considerations"
%%%

Coercions are a powerful tool that should be used responsibly.
On the one hand, they can allow an API to naturally follow the everyday rules of the domain being modeled.
This can be the difference between a bureaucratic mess of manual conversion functions and a clear program.
As Abelson and Sussman wrote in the preface to _Structure and Interpretation of Computer Programs_ (MIT Press, 1996),

> Programs must be written for people to read, and only incidentally for machines to execute.

Coercions, used wisely, are a valuable means of achieving readable code that can serve as the basis for communication with domain experts.
APIs that rely heavily on coercions have a number of important limitations, however.
Think carefully about these limitations before using coercions in your own libraries.

First off, coercions are only applied in contexts where enough type information is available for Lean to know all of the types involved, because there are no output parameters in the coercion type classes. This means that a return type annotation on a function can be the difference between a type error and a successfully applied coercion.
For example, the coercion from non-empty lists to lists makes the following program work:

```anchor lastSpiderA
def lastSpider : Option String :=
  List.getLast? idahoSpiders
```
On the other hand, if the type annotation is omitted, then the result type is unknown, so Lean is unable to find the coercion:
```anchor lastSpiderB
def lastSpider :=
  List.getLast? idahoSpiders
```
```anchorError lastSpiderB
Application type mismatch: The argument
  idahoSpiders
has type
  NonEmptyList String
but is expected to have type
  List ?m.3
in the application
  List.getLast? idahoSpiders
```
More generally, when a coercion is not applied for some reason, the user receives the original type error, which can make it difficult to debug chains of coercions.

Finally, coercions are not applied in the context of field accessor notation.
This means that there is still an important difference between expressions that need to be coerced and those that don't, and this difference is visible to users of your API.
