import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "Applicative Functors" =>
%%%
tag := "applicative"
%%%

An _applicative functor_ is a functor that has two additional operations available: {anchorName ApplicativeOption}`pure` and {anchorName ApplicativeOption}`seq`.
{anchorName ApplicativeOption}`pure` is the same operator used in {anchorName ApplicativeLaws}`Monad`, because {anchorName ApplicativeLaws}`Monad` in fact inherits from {anchorName ApplicativeOption}`Applicative`.
{anchorName ApplicativeOption}`seq` is much like {anchorName FunctorNames}`map`: it allows a function to be used in order to transform the contents of a datatype.
However, with {anchorName ApplicativeOption}`seq`, the function is itself contained in the datatype: {anchorTerm seqType}`f (α → β) → (Unit → f α) → f β`.
Having the function under the type {anchorName seqType}`f` allows the {anchorName ApplicativeOption}`Applicative` instance to control how the function is applied, while {anchorName FunctorNames}`Functor.map` unconditionally applies a function.
The second argument has a type that begins with {anchorTerm seqType}`Unit →` to allow the definition of {anchorName ApplicativeOption}`seq` to short-circuit in cases where the function will never be applied.

The value of this short-circuiting behavior can be seen in the instance of {anchorTerm ApplicativeOption}`Applicative Option`:

```anchor ApplicativeOption
instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()
```
In this case, if there is no function for {anchorName ApplicativeOption}`seq` to apply, then there is no need to compute its argument, so {anchorName ApplicativeOption}`x` is never called.
The same consideration informs the instance of {anchorName ApplicativeExcept}`Applicative` for {anchorName ApplicativeExcept}`Except`:

```anchor ApplicativeExcept
instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok g => g <$> x ()
```
This short-circuiting behavior depends only on the {anchorName AlternativeOption}`Option` or {anchorName ApplicativeExcept}`Except` structures that _surround_ the function, rather than on the function itself.

Monads can be seen as a way of capturing the notion of sequentially executing statements into a pure functional language.
The result of one statement can affect which further statements run.
This can be seen in the type of {anchorName bindType}`bind`: {anchorTerm bindType}`m α → (α → m β) → m β`.
The first statement's resulting value is an input into a function that computes the next statement to execute.
Successive uses of {anchorName bindType}`bind` are like a sequence of statements in an imperative programming language, and {anchorName bindType}`bind` is powerful enough to implement control structures like conditionals and loops.

Following this analogy, {anchorName ApplicativeId}`Applicative` captures function application in a language that has side effects.
The arguments to a function in languages like Kotlin or C# are evaluated from left to right.
Side effects performed by earlier arguments occur before those performed by later arguments.
A function is not powerful enough to implement custom short-circuiting operators that depend on the specific _value_ of an argument, however.

Typically, {anchorName ApplicativeExtendsFunctorOne}`seq` is not invoked directly.
Instead, the operator {lit}`<*>` is used.
This operator wraps its second argument in {lit}`fun () => ...`, simplifying the call site.
In other words, {anchorTerm seqSugar}`E1 <*> E2` is syntactic sugar for {anchorTerm seqSugar}`Seq.seq E1 (fun () => E2)`.


The key feature that allows {anchorName ApplicativeExtendsFunctorOne}`seq` to be used with multiple arguments is that a multiple-argument Lean function is really a single-argument function that returns another function that's waiting for the rest of the arguments.
In other words, if the first argument to {anchorName ApplicativeExtendsFunctorOne}`seq` is awaiting multiple arguments, then the result of the {anchorName ApplicativeExtendsFunctorOne}`seq` will be awaiting the rest.
For example, {anchorTerm somePlus}`some Plus.plus` can have the type {anchorTerm somePlus}`Option (Nat → Nat → Nat)`.
Providing one argument, {anchorTerm somePlusFour}`some Plus.plus <*> some 4`, results in the type {anchorTerm somePlusFour}`Option (Nat → Nat)`.
This can itself be used with {anchorName ApplicativeExtendsFunctorOne}`seq`, so {anchorTerm somePlusFourSeven}`some Plus.plus <*> some 4 <*> some 7` has the type {anchorTerm somePlusFourSeven}`Option Nat`.

Not every functor is applicative.
{anchorName Pair}`Pair` is like the built-in product type {anchorName names}`Prod`:

```anchor Pair
structure Pair (α β : Type) : Type where
  first : α
  second : β
```
Like {anchorName ApplicativeExcept}`Except`, {anchorTerm PairType}`Pair` has type {anchorTerm PairType}`Type → Type → Type`.
This means that {anchorTerm FunctorPair}`Pair α` has type {anchorTerm PairType}`Type → Type`, and a {anchorName FunctorPair}`Functor` instance is possible:

```anchor FunctorPair
instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩
```
This instance obeys the {anchorName FunctorPair}`Functor` contract.

The two properties to check are that {anchorEvalStep checkPairMapId 0}`id <$> Pair.mk x y`{lit}` = `{anchorEvalStep checkPairMapId 2}`Pair.mk x y` and that {anchorEvalStep checkPairMapComp1 0}`f <$> g <$> Pair.mk x y`{lit}` = `{anchorEvalStep checkPairMapComp2 0}`(f ∘ g) <$> Pair.mk x y`.
The first property can be checked by just stepping through the evaluation of the left side, and noticing that it evaluates to the right side:
```anchorEvalSteps checkPairMapId
id <$> Pair.mk x y
===>
Pair.mk x (id y)
===>
Pair.mk x y
```
The second can be checked by stepping through both sides, and noting that they yield the same result:
```anchorEvalSteps checkPairMapComp1
f <$> g <$> Pair.mk x y
===>
f <$> Pair.mk x (g y)
===>
Pair.mk x (f (g y))
```
```anchorEvalSteps checkPairMapComp2
(f ∘ g) <$> Pair.mk x y
===>
Pair.mk x ((f ∘ g) y)
===>
Pair.mk x (f (g y))
```

Attempting to define an {anchorName ApplicativeExcept}`Applicative` instance, however, does not work so well.
It will require a definition of {anchorName Pairpure (show := pure)}`Pair.pure`:
```anchor Pairpure
def Pair.pure (x : β) : Pair α β := _
```
```anchorError Pairpure
don't know how to synthesize placeholder
context:
β α : Type
x : β
⊢ Pair α β
```
There is a value with type {anchorName Pairpure2}`β` in scope (namely {anchorName Pairpure2}`x`), and the error message from the underscore suggests that the next step is to use the constructor {anchorName Pairpure2}`Pair.mk`:
```anchor Pairpure2
def Pair.pure (x : β) : Pair α β := Pair.mk _ x
```
```anchorError Pairpure2
don't know how to synthesize placeholder for argument 'first'
context:
β α : Type
x : β
⊢ α
```
Unfortunately, there is no {anchorName Pairpure2}`α` available.
Because {anchorName Pairpure2 (show := pure)}`Pair.pure` would need to work for _all possible types_ {anchorName Pairpure2}`α` to define an instance of {anchorTerm ApplicativePair}`Applicative (Pair α)`, this is impossible.
After all, a caller could choose {anchorName Pairpure2}`α` to be {anchorName ApplicativePair}`Empty`, which has no values at all.

# A Non-Monadic Applicative
%%%
tag := "validate"
%%%

When validating user input to a form, it's generally considered to be best to provide many errors at once, rather than one error at a time.
This allows the user to have an overview of what is needed to please the computer, rather than feeling badgered as they correct the errors field by field.

Ideally, validating user input will be visible in the type of the function that's doing the validating.
It should return a datatype that is specific—checking that a text box contains a number should return an actual numeric type, for instance.
A validation routine could throw an exception when the input does not pass validation.
Exceptions have a major drawback, however: they terminate the program at the first error, making it impossible to accumulate a list of errors.

On the other hand, the common design pattern of accumulating a list of errors and then failing when it is non-empty is also problematic.
A long nested sequences of {kw}`if` statements that validate each sub-section of the input data is hard to maintain, and it's easy to lose track of an error message or two.
Ideally, validation can be performed using an API that enables a new value to be returned yet automatically tracks and accumulates error messages.

An applicative functor called {anchorName Validate}`Validate` provides one way to implement this style of API.
Like the {anchorName ApplicativeExcept}`Except` monad, {anchorName Validate}`Validate` allows a new value to be constructed that characterizes the validated data accurately.
Unlike {anchorName ApplicativeExcept}`Except`, it allows multiple errors to be accumulated, without a risk of forgetting to check whether the list is empty.

## User Input
%%%
tag := "user-input"
%%%
As an example of user input, take the following structure:

```anchor RawInput
structure RawInput where
  name : String
  birthYear : String
```
The business logic to be implemented is the following:
 1. The name may not be empty
 2. The birth year must be numeric and non-negative
 3. The birth year must be greater than 1900, and less than or equal to the year in which the form is validated

Representing these as a datatype will require a new feature, called _subtypes_.
With this tool in hand, a validation framework can be written that uses an applicative functor to track errors, and these rules can be implemented in the framework.

## Subtypes
%%%
tag := "subtypes"
%%%

Representing these conditions is easiest with one additional Lean type, called {anchorName Subtype}`Subtype`:

```anchor Subtype
structure Subtype {α : Type} (p : α → Prop) where
  val : α
  property : p val
```
This structure has two type parameters: an implicit parameter that is the type of data {anchorName Subtype}`α`, and an explicit parameter {anchorName Subtype}`p` that is a predicate over {anchorName Subtype}`α`.
A _predicate_ is a logical statement with a variable in it that can be replaced with a value to yield an actual statement, like the {ref "overloading-indexing"}[parameter to {moduleName}`GetElem`] that describes what it means for an index to be in bounds for a lookup.
In the case of {anchorName Subtype}`Subtype`, the predicate slices out some subset of the values of {anchorName Subtype}`α` for which the predicate holds.
The structure's two fields are, respectively, a value from {anchorName Subtype}`α` and evidence that the value satisfies the predicate {anchorName Subtype}`p`.
Lean has special syntax for {anchorName Subtype}`Subtype`.
If {anchorName Subtype}`p` has type {anchorTerm Subtype}`α → Prop`, then the type {anchorTerm subtypeSugarIn}`Subtype p` can also be written {anchorTerm subtypeSugar}`{x : α // p x}`, or even {anchorTerm subtypeSugar2}`{x // p x}` when the type {anchorName Subtype}`α` can be inferred automatically.

{ref "positive-numbers"}[Representing positive numbers as inductive types] is clear and easy to program with.
However, it has a key disadvantage.
While {anchorName names}`Nat` and {anchorName names}`Int` have the structure of ordinary inductive types from the perspective of Lean programs, the compiler treats them specially and uses fast arbitrary-precision number libraries to implement them.
This is not the case for additional user-defined types.
However, a subtype of {anchorName names}`Nat` that restricts it to non-zero numbers allows the new type to use the efficient representation while still ruling out zero at compile time:

```anchor FastPos
def FastPos : Type := {x : Nat // x > 0}
```

The smallest fast positive number is still one.
Now, instead of being a constructor of an inductive type, it's an instance of a structure that's constructed with angle brackets.
The first argument is the underlying {anchorName FastPos}`Nat`, and the second argument is the evidence that said {anchorName FastPos}`Nat` is greater than zero:

```anchor one
def one : FastPos := ⟨1, by decide⟩
```
The proposition {anchorTerm onep}`1 > 0` is decidable, so the {tactic}`decide` tactic produces the necessary evidence.
The {anchorName OfNatFastPos}`OfNat` instance is very much like that for {anchorName Pos (module:=Examples.Classes)}`Pos`, except it uses a short tactic proof to provide evidence that {lit}`n + 1 > 0`:

```anchor OfNatFastPos
instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp⟩
```
Here, {tactic}`simp` is needed because {tactic}`decide` requires concrete values, but the proposition in question is {anchorTerm OfNatFastPosp}`n + 1 > 0`.

Subtypes are a two-edged sword.
They allow efficient representation of validation rules, but they transfer the burden of maintaining these rules to the users of the library, who have to _prove_ that they are not violating important invariants.
Generally, it's a good idea to use them internally to a library, providing an API to users that automatically ensures that all invariants are satisfied, with any necessary proofs being internal to the library.

Checking whether a value of type {anchorName NatFastPosRemarks}`α` is in the subtype {anchorTerm NatFastPosRemarks}`{x : α // p x}` usually requires that the proposition {anchorTerm NatFastPosRemarks}`p x` be decidable.
The {ref "equality-and-ordering"}[section on equality and ordering classes] describes how decidable propositions can be used with {kw}`if`.
When {kw}`if` is used with a decidable proposition, a name can be provided.
In the {kw}`then` branch, the name is bound to evidence that the proposition is true, and in the {kw}`else` branch, it is bound to evidence that the proposition is false.
This comes in handy when checking whether a given {anchorName NatFastPos}`Nat` is positive:

```anchor NatFastPos
def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none
```
In the {kw}`then` branch, {anchorName NatFastPos}`h` is bound to evidence that {anchorTerm NatFastPos}`n > 0`, and this evidence can be used as the second argument to {anchorName Subtype}`Subtype`'s constructor.


## Validated Input
%%%
tag := "validated-input"
%%%

The validated user input is a structure that expresses the business logic using multiple techniques:
 * The structure type itself encodes the year in which it was checked for validity, so that {anchorTerm CheckedInputEx}`CheckedInput 2019` is not the same type as {anchorTerm CheckedInputEx}`CheckedInput 2020`
 * The birth year is represented as a {anchorName CheckedInput}`Nat` rather than a {anchorName CheckedInput}`String`
 * Subtypes are used to constrain the allowed values in the name and birth year fields

```anchor CheckedInput
structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
```

:::paragraph
An input validator should take the current year and a {anchorName RawInput}`RawInput` as arguments, returning either a checked input or at least one validation failure.
This is represented by the {anchorName Validate}`Validate` type:
```anchor Validate
inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
```
It looks very much like {anchorName ApplicativeExcept}`Except`.
The only difference is that the {anchorName Validate}`errors` constructor may contain more than one failure.
:::

{anchorName Validate}`Validate` is a functor.
Mapping a function over it transforms any successful value that might be present, just as in the {anchorName FunctorValidate}`Functor` instance for {anchorName ApplicativeExcept}`Except`:

```anchor FunctorValidate
instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs
```

The {anchorName ApplicativeValidate}`Applicative` instance for {anchorName ApplicativeValidate}`Validate` has an important difference from the instance for {anchorName ApplicativeExcept}`Except`: while the instance for {anchorName ApplicativeExcept}`Except` terminates at the first error encountered, the instance for {anchorName ApplicativeValidate}`Validate` is careful to accumulate all errors from _both_ the function and the argument branches:

```anchor ApplicativeValidate
instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')
```

:::paragraph
Using {anchorName ApplicativeValidate}`.errors` together with the constructor for {anchorName Validate}`NonEmptyList` is a bit verbose.
Helpers like {anchorName reportError}`reportError` make code more readable.
In this application, error reports will consist of field names paired with messages:

```anchor Field
def Field := String
```

```anchor reportError
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }
```
:::

The {anchorName ApplicativeValidate}`Applicative` instance for {anchorName ApplicativeValidate}`Validate` allows the checking procedures for each field to be written independently and then composed.
Checking a name consists of ensuring that a string is non-empty, then returning evidence of this fact in the form of a {anchorName Subtype}`Subtype`.
This uses the evidence-binding version of {kw}`if`:

```anchor checkName
def checkName (name : String) :
    Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩
```
In the {kw}`then` branch, {anchorName checkName}`h` is bound to evidence that {anchorTerm checkName}`name = ""`, while it is bound to evidence that {lit}`¬name = ""` in the {kw}`else` branch.

It's certainly the case that some validation errors make other checks impossible.
For example, it makes no sense to check whether the birth year field is greater than 1900 if a confused user wrote the word {anchorTerm checkDavidSyzygy}`"syzygy"` instead of a number.
Checking the allowed range of the number is only meaningful after ensuring that the field in fact contains a number.
This can be expressed using the function {anchorName ValidateAndThen (show := andThen)}`Validate.andThen`:

```anchor ValidateAndThen
def Validate.andThen (val : Validate ε α)
    (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x
```
While this function's type signature makes it suitable to be used as {anchorName bindType}`bind` in a {anchorTerm bindType}`Monad` instance, there are good reasons not to do so.
They are described {ref "additional-stipulations"}[in the section that describes the {anchorName ApplicativeExcept}`Applicative` contract].

To check that the birth year is a number, a built-in function called {anchorTerm CheckedInputEx}`String.toNat? : String → Option Nat` is useful.
It's most user-friendly to eliminate leading and trailing whitespace first using {anchorName CheckedInputEx}`String.trim`:

```anchor checkYearIsNat
def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n
```

:::paragraph
To check that the provided year is in the expected range, nested uses of the evidence-providing form of {kw}`if` are in order:

```anchor checkBirthYear
def checkBirthYear (thisYear year : Nat) :
    Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"
```
:::

:::paragraph
Finally, these three components can be combined using {anchorTerm checkInput}`<*>`:

```anchor checkInput
def checkInput (year : Nat) (input : RawInput) :
    Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat
```
:::

:::paragraph
Testing {anchorName checkDavid1984}`checkInput` shows that it can indeed return multiple pieces of feedback:
```anchor checkDavid1984
#eval checkInput 2023 {name := "David", birthYear := "1984"}
```
```anchorInfo checkDavid1984
Validate.ok { name := "David", birthYear := 1984 }
```
```anchor checkBlank2045
#eval checkInput 2023 {name := "", birthYear := "2045"}
```
```anchorInfo checkBlank2045
Validate.errors { head := ("name", "Required"), tail := [("birth year", "Must be no later than 2023")] }
```
```anchor checkDavidSyzygy
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}
```
```anchorInfo checkDavidSyzygy
Validate.errors { head := ("birth year", "Must be digits"), tail := [] }
```
:::

Form validation with {anchorName checkInput}`checkInput` illustrates a key advantage of {anchorName ApplicativeNames}`Applicative` over {anchorName MonadExtends}`Monad`.
Because {lit}`>>=` provides enough power to modify the rest of the program's execution based on the value from the first step, it _must_ receive a value from the first step to pass on.
If no value is received (e.g. because an error has occurred), then {lit}`>>=` cannot execute the rest of the program.
{anchorName Validate}`Validate` demonstrates why it can be useful to run the rest of the program anyway: in cases where the earlier data isn't needed, running the rest of the program can yield useful information (in this case, more validation errors).
{anchorName ApplicativeNames}`Applicative`'s {lit}`<*>` may run both of its arguments before recombining the results.
Similarly, {lit}`>>=` forces sequential execution.
Each step must complete before the next may run.
This is generally useful, but it makes it impossible to have parallel execution of different threads that naturally emerges from the program's actual data dependencies.
A more powerful abstraction like {anchorName MonadExtends}`Monad` increases the flexibility that's available to the API consumer, but it decreases the flexibility that is available to the API implementor.
