import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Positive Numbers" =>
%%%
tag := "positive-numbers"
%%%

In some applications, only positive numbers make sense.
For example, compilers and interpreters typically use one-indexed line and column numbers for source positions, and a datatype that represents only non-empty lists will never report a length of zero.
Rather than relying on natural numbers, and littering the code with assertions that the number is not zero, it can be useful to design a datatype that represents only positive numbers.

One way to represent positive numbers is very similar to {anchorTerm chapterIntro}`Nat`, except with {anchorTerm Pos}`one` as the base case instead of {anchorTerm Nat.zero}`zero`:

```anchor Pos
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
```
This datatype represents exactly the intended set of values, but it is not very convenient to use.
For example, numeric literals are rejected:
```anchor sevenOops
def seven : Pos := 7
```
```anchorError sevenOops
failed to synthesize
  OfNat Pos 7
numerals are polymorphic in Lean, but the numeral `7` cannot be used in a context where the expected type is
  Pos
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
Instead, the constructors must be used directly:
```anchor seven
def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
```

Similarly, addition and multiplication are not easy to use:
```anchor fourteenOops
def fourteen : Pos := seven + seven
```
```anchorError fourteenOops
failed to synthesize
  HAdd Pos Pos ?m.3

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```anchor fortyNineOops
def fortyNine : Pos := seven * seven
```
```anchorError fortyNineOops
failed to synthesize
  HMul Pos Pos ?m.3

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

Each of these error messages begins with {lit}`failed to synthesize`.
This indicates that the error is due to an overloaded operation that has not been implemented, and it describes the type class that must be implemented.

# Classes and Instances
%%%
tag := "classes-and-instances"
%%%

A type class consists of a name, some parameters, and a collection of {deftech}_methods_.
The parameters describe the types for which overloadable operations are being defined, and the methods are the names and type signatures of the overloadable operations.
Once again, there is a terminology clash with object-oriented languages.
In object-oriented programming, a method is essentially a function that is connected to a particular object in memory, with special access to the object's private state.
Objects are interacted with via their methods.
In Lean, the term “method” refers to an operation that has been declared to be overloadable, with no special connection to objects or values or private fields.

One way to overload addition is to define a type class named {anchorName Plus}`Plus`, with an addition method named {anchorName Plus}`plus`.
Once an instance of {anchorTerm Plus}`Plus` for {anchorTerm chapterIntro}`Nat` has been defined, it becomes possible to add two {anchorTerm chapterIntro}`Nat`s using {anchorName plusNatFiveThree}`Plus.plus`:
```anchor plusNatFiveThree
#eval Plus.plus 5 3
```
```anchorInfo plusNatFiveThree
8
```
Adding more instances allows {anchorName plusNatFiveThree}`Plus.plus` to take more types of arguments.

In the following type class declaration, {anchorName Plus}`Plus` is the name of the class, {anchorTerm Plus}`α : Type` is the only argument, and {anchorTerm Plus}`plus : α → α → α` is the only method:

```anchor Plus
class Plus (α : Type) where
  plus : α → α → α
```
This declaration says that there is a type class {anchorName Plus}`Plus` that overloads operations with respect to a type {anchorName Plus}`α`.
In particular, there is one overloaded operation called {anchorName Plus}`plus` that takes two {anchorName Plus}`α`s and returns an {anchorName Plus}`α`.

Type classes are first class, just as types are first class.
In particular, a type class is another kind of type.
The type of {anchorTerm PlusType}`Plus` is {anchorTerm PlusType}`Type → Type`, because it takes a type as an argument ({anchorName Plus}`α`) and results in a new type that describes the overloading of {anchorName Plus}`Plus`'s operation for {anchorName Plus}`α`.


To overload {anchorName PlusNat}`plus` for a particular type, write an instance:

```anchor PlusNat
instance : Plus Nat where
  plus := Nat.add
```
The colon after {anchorTerm PlusNat}`instance` indicates that {anchorTerm PlusNat}`Plus Nat` is indeed a type.
Each method of class {anchorName Plus}`Plus` should be assigned a value using {anchorTerm PlusNat}`:=`.
In this case, there is only one method: {anchorName PlusNat}`plus`.

By default, type class methods are defined in a namespace with the same name as the type class.
It can be convenient to {anchorTerm openPlus}`open` the namespace so that users don't need to type the name of the class first.
Parentheses in an {kw}`open` command indicate that only the indicated names from the namespace are to be made accessible:

```anchor openPlus
open Plus (plus)
```
```anchor plusNatFiveThreeAgain
#eval plus 5 3
```
```anchorInfo plusNatFiveThreeAgain
8
```

Defining an addition function for {anchorName PlusPos}`Pos` and an instance of {anchorTerm PlusPos}`Plus Pos` allows {anchorName PlusPos}`plus` to be used to add both {anchorName PlusPos}`Pos` and {anchorTerm chapterIntro}`Nat` values:

```anchor PlusPos
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven
```

Because there is not yet an instance of {anchorTerm PlusFloat}`Plus Float`, attempting to add two floating-point numbers with {anchorName plusFloatFail}`plus` fails with a familiar message:
```anchor plusFloatFail
#eval plus 5.2 917.25861
```
```anchorError plusFloatFail
failed to synthesize
  Plus Float

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
These errors mean that Lean was unable to find an instance for a given type class.

# Overloaded Addition
%%%
tag := "overloaded-addition"
%%%

Lean's built-in addition operator is syntactic sugar for a type class called {anchorName chapterIntro}`HAdd`, which flexibly allows the arguments to addition to have different types.
{anchorName chapterIntro}`HAdd` is short for _heterogeneous addition_.
For example, an {anchorName chapterIntro}`HAdd` instance can be written to allow a {anchorName chapterIntro}`Nat` to be added to a {anchorName fiveZeros}`Float`, resulting in a new {anchorName fiveZeros}`Float`.
When a programmer writes {anchorTerm plusDesugar}`x + y`, it is interpreted as meaning {anchorTerm plusDesugar}`HAdd.hAdd x y`.

While an understanding of the full generality of {anchorName chapterIntro}`HAdd` relies on features that are discussed in {ref "out-params"}[another section in this chapter], there is a simpler type class called {anchorName AddPos}`Add` that does not allow the types of the arguments to be mixed.
The Lean libraries are set up so that an instance of {anchorName AddPos}`Add` will be found when searching for an instance of {anchorName chapterIntro}`HAdd` in which both arguments have the same type.

Defining an instance of {anchorTerm AddPos}`Add Pos` allows {anchorTerm AddPos}`Pos` values to use ordinary addition syntax:

```anchor AddPos
instance : Add Pos where
  add := Pos.plus
```
```anchor betterFourteen
def fourteen : Pos := seven + seven
```

# Conversion to Strings
%%%
tag := "conversion-to-strings"
%%%

Another useful built-in class is called {anchorName UglyToStringPos}`ToString`.
Instances of {anchorName UglyToStringPos}`ToString` provide a standard way of converting values from a given type into strings.
For example, a {anchorName UglyToStringPos}`ToString` instance is used when a value occurs in an interpolated string, and it determines how the {anchorName printlnType}`IO.println` function used at the {ref "running-a-program"}[beginning of the description of {anchorName readFile}`IO`] will display a value.

For example, one way to convert a {anchorName Pos}`Pos` into a {anchorName readFile}`String` is to reveal its inner structure.
The function {anchorName posToStringStructure}`posToString` takes a {anchorName posToStringStructure}`Bool` that determines whether to parenthesize uses of {anchorName posToStringStructure}`Pos.succ`, which should be {anchorName CoeBoolProp}`true` in the initial call to the function and {anchorName posToStringStructure}`false` in all recursive calls.

```anchor posToStringStructure
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
```
Using this function for a {anchorName UglyToStringPos}`ToString` instance:

```anchor UglyToStringPos
instance : ToString Pos where
  toString := posToString true
```
results in informative, yet overwhelming, output:
```anchor sevenLong
#eval s!"There are {seven}"
```
```anchorInfo sevenLong
"There are Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))"
```

On the other hand, every positive number has a corresponding {anchorTerm chapterIntro}`Nat`.
Converting it to a {anchorTerm chapterIntro}`Nat` and then using the {anchorTerm chapterIntro}`ToString Nat` instance (that is, the overloading of {anchorName UglyToStringPos}`ToString` for {anchorTerm chapterIntro}`Nat`) is a quick way to generate much shorter output:

```anchor posToNat
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
```
```anchor PosToStringNat
instance : ToString Pos where
  toString x := toString (x.toNat)
```
```anchor sevenShort
#eval s!"There are {seven}"
```
```anchorInfo sevenShort
"There are 7"
```
When more than one instance is defined, the most recent takes precedence.
Additionally, if a type has a {anchorName UglyToStringPos}`ToString` instance, then it can be used to display the result of {kw}`#eval` so {anchorTerm sevenEvalStr}`#eval seven` outputs {anchorInfo sevenEvalStr}`7`.

# Overloaded Multiplication
%%%
tag := "overloaded-multiplication"
%%%

For multiplication, there is a type class called {anchorName MulPPoint}`HMul` that allows mixed argument types, just like {anchorName chapterIntro}`HAdd`.
Just as {anchorTerm plusDesugar}`x + y` is interpreted as {anchorTerm plusDesugar}[`HAdd.hAdd x y`], {anchorTerm timesDesugar}`x * y` is interpreted as {anchorTerm timesDesugar}`HMul.hMul x y`.
For the common case of multiplication of two arguments with the same type, a {anchorName PosMul}`Mul` instance suffices.

An instance of {anchorTerm PosMul}`Mul` allows ordinary multiplication syntax to be used with {anchorName PosMul}`Pos`:

```anchor PosMul
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul
```
With this instance, multiplication works as expected:
```anchor muls
#eval [seven * Pos.one,
       seven * seven,
       Pos.succ Pos.one * seven]
```
```anchorInfo muls
[7, 49, 14]
```

# Literal Numbers
%%%
tag := "literal-numbers"
%%%

It is quite inconvenient to write out a sequence of constructors for positive numbers.
One way to work around the problem would be to provide a function to convert a {anchorTerm chapterIntro}`Nat` into a {anchorName Pos}`Pos`.
However, this approach has downsides.
First off, because {anchorName PosMul}`Pos` cannot represent {anchorTerm nats}`0`, the resulting function would either convert a {anchorTerm chapterIntro}`Nat` to a bigger number, or it would return {anchorTerm PosStuff}`Option Pos`.
Neither is particularly convenient for users.
Secondly, the need to call the function explicitly would make programs that use positive numbers much less convenient to write than programs that use {anchorTerm chapterIntro}`Nat`.
Having a trade-off between precise types and convenient APIs means that the precise types become less useful.

There are three type classes that are used to overload numeric literals: {anchorName Zero}`Zero`, {anchorName One}`One`, and {anchorName OfNat}`OfNat`.
Because many types have values that are naturally written with {anchorTerm nats}`0`, the {anchorName Zero}`Zero` class allow these specific values to be overridden.
It is defined as follows:

```anchor Zero
class Zero (α : Type) where
  zero : α
```
Because {anchorTerm nats}`0` is not a positive number, there should be no instance of {anchorTerm PosStuff}`Zero Pos`.

Similarly, many types have values that are naturally written with {anchorTerm nats}`1`.
The {anchorName One}`One` class allows these to be overridden:
```anchor One
class One (α : Type) where
  one : α
```
An instance of {anchorTerm OnePos}`One Pos` makes perfect sense:
```anchor OnePos
instance : One Pos where
  one := Pos.one
```
With this instance, {anchorTerm onePos}`1` can be used for {anchorTerm OnePos}`Pos.one`:
```anchor onePos
#eval (1 : Pos)
```
```anchorInfo onePos
1
```

In Lean, natural number literals are interpreted using a type class called {anchorName OfNat}`OfNat`:

```anchor OfNat
class OfNat (α : Type) (_ : Nat) where
  ofNat : α
```
This type class takes two arguments: {anchorTerm OfNat}`α` is the type for which a natural number is overloaded, and the unnamed {anchorTerm chapterIntro}`Nat` argument is the actual literal number that was encountered in the program.
The method {anchorName OfNat}`ofNat` is then used as the value of the numeric literal.
Because the class contains the {anchorTerm chapterIntro}`Nat` argument, it becomes possible to define only instances for those values where the number makes sense.

{anchorTerm OfNat}`OfNat` demonstrates that the arguments to type classes do not need to be types.
Because types in Lean are first-class participants in the language that can be passed as arguments to functions and given definitions with {kw}`def` and {kw}`abbrev`, there is no barrier that prevents non-type arguments in positions where a less-flexible language could not permit them.
This flexibility allows overloaded operations to be provided for particular values as well as particular types.
Additionally, it allows the Lean standard library to arrange for there to be a {anchorTerm ListSumZ}`Zero α` instance whenever there's an {anchorTerm ListSum}`OfNat α 0` instance, and vice versa.
Similarly, an instance of {anchorTerm OneExamples}`One α` implies an instance of {anchorTerm OneExamples}`OfNat α 1`, just as an instance of {anchorTerm OneExamples}`OfNat α 1` implies an instance of {anchorTerm OneExamples}`One α`.

A sum type that represents natural numbers less than four can be defined as follows:

```anchor LT4
inductive LT4 where
  | zero
  | one
  | two
  | three
```
While it would not make sense to allow _any_ literal number to be used for this type, numbers less than four clearly make sense:

```anchor LT4ofNat
instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three
```
With these instances, the following examples work:
```anchor LT4three
#eval (3 : LT4)
```
```anchorInfo LT4three
LT4.three
```
```anchor LT4zero
#eval (0 : LT4)
```
```anchorInfo LT4zero
LT4.zero
```
On the other hand, out-of-bounds literals are still not allowed:
```anchor LT4four
#eval (4 : LT4)
```
```anchorError LT4four
failed to synthesize
  OfNat LT4 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  LT4
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

For {anchorName PosMul}`Pos`, the {anchorTerm OfNat}`OfNat` instance should work for _any_ {anchorTerm chapterIntro}`Nat` other than {anchorName PosStuff}`Nat.zero`.
Another way to phrase this is to say that for all natural numbers {anchorTerm posrec}`n`, the instance should work for {anchorTerm posrec}`n + 1`.
Just as names like {anchorTerm posrec}`α` automatically become implicit arguments to functions that Lean fills out on its own, instances can take automatic implicit arguments.
In this instance, the argument {anchorTerm OfNatPos}`n` stands for any {anchorTerm chapterIntro}`Nat`, and the instance is defined for a {anchorTerm chapterIntro}`Nat` that's one greater:

```anchor OfNatPos
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n
```
Because {anchorTerm OfNatPos}`n` stands for a {anchorTerm chapterIntro}`Nat` that's one less than what the user wrote, the helper function {anchorName OfNatPos}`natPlusOne` returns a {anchorName OfNatPos}`Pos` that's one greater than its argument.
This makes it possible to use natural number literals for positive numbers, but not for zero:

```anchor eight
def eight : Pos := 8
```
```anchor zeroBad
def zero : Pos := 0
```
```anchorError zeroBad
failed to synthesize
  OfNat Pos 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Pos
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

# Exercises
%%%
tag := "positive-numbers-exercises"
%%%

## Another Representation
%%%
tag := "positive-numbers-another-representation"
%%%

An alternative way to represent a positive number is as the successor of some {anchorTerm chapterIntro}`Nat`.
Replace the definition of {anchorName PosStuff}`Pos` with a structure whose constructor is named {anchorName AltPos}`succ` that contains a {anchorTerm chapterIntro}`Nat`:

```anchor AltPos
structure Pos where
  succ ::
  pred : Nat
```
Define instances of {moduleName}`Add`, {moduleName}`Mul`, {anchorName UglyToStringPos}`ToString`, and {moduleName}`OfNat` that allow this version of {anchorName AltPos}`Pos` to be used conveniently.

## Even Numbers
%%%
tag := "even-numbers-ex"
%%%

Define a datatype that represents only even numbers. Define instances of {moduleName}`Add`, {moduleName}`Mul`, and {anchorName UglyToStringPos}`ToString` that allow it to be used conveniently.
{moduleName}`OfNat` requires a feature that is introduced in {ref "tc-polymorphism"}[the next section].

## HTTP Requests
%%%
tag := "http-request-ex"
%%%

An HTTP request begins with an identification of a HTTP method, such as {lit}`GET` or {lit}`POST`, along with a URI and an HTTP version.
Define an inductive type that represents an interesting subset of the HTTP methods, and a structure that represents HTTP responses.
Responses should have a {anchorName UglyToStringPos}`ToString` instance that makes it possible to debug them.
Use a type class to associate different {moduleName}`IO` actions with each HTTP method, and write a test harness as an {moduleName}`IO` action that calls each method and prints the result.
