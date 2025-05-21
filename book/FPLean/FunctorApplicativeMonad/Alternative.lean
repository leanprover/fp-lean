import VersoManual
import FPLean.Examples

open Verso.Genre Manual ExternalLean

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "Alternatives" =>


# Recovery from Failure

`Validate` can also be used in situations where there is more than one way for input to be acceptable.
For the input form `RawInput`, an alternative set of business rules that implement conventions from a legacy system might be the following:

 1. All human users must provide a birth year that is four digits.
 2. Users born prior to 1970 do not need to provide names, due to incomplete older records.
 3. Users born after 1970 must provide names.
 4. Companies should enter `"FIRM"` as their year of birth and provide a company name.

No particular provision is made for users born in 1970.
It is expected that they will either give up, lie about their year of birth, or call.
The company considers this an acceptable cost of doing business.

The following inductive type captures the values that can be produced from these stated rules:

```anchor LegacyCheckedInput
abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr
```

A validator for these rules is more complicated, however, as it must address all three cases.
While it can be written as a series of nested {kw}`if` expressions, it's easier to design the three cases independently and then combine them.
This requires a means of recovering from failure while preserving error messages:

```anchor ValidateorElse
def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)
```

This pattern of recovery from failures is common enough that Lean has built-in syntax for it, attached to a type class named `OrElse`:

```anchor OrElse
class OrElse (α : Type) where
  orElse : α → (Unit → α) → α
```
The expression {anchorTerm OrElseSugar}`E1 <|> E2` is short for {anchorTerm OrElseSugar}`OrElse.orElse E1 (fun () => E2)`.
An instance of `OrElse` for `Validate` allows this syntax to be used for error recovery:

```anchor OrElseValidate
instance : OrElse (Validate ε α) where
  orElse := Validate.orElse
```

The validator for `LegacyCheckedInput` can be built from a validator for each constructor.
The rules for a company state that the birth year should be the string `"FIRM"` and that the name should be non-empty.
The constructor `LegacyCheckedInput.company`, however, has no representation of the birth year at all, so there's no easy way to carry it out using `<*>`.
The key is to use a function with `<*>` that ignores its argument.

Checking that a Boolean condition holds without recording any evidence of this fact in a type can be accomplished with `checkThat`:

```anchor checkThat
def checkThat (condition : Bool) (field : Field) (msg : String) : Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg
```
This definition of `checkCompany` uses `checkThat`, and then throws away the resulting `Unit` value:

```anchor checkCompanyProv
def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" <*>
    checkName input.name
```

However, this definition is quite noisy.
It can be simplified in two ways.
The first is to replace the first use of `<*>` with a specialized version that automatically ignores the value returned by the first argument, called `*>`.
This operator is also controlled by a type class, called `SeqRight`, and {anchorTerm seqRightSugar}`E1 *> E2` is syntactic sugar for {anchorTerm seqRightSugar}`SeqRight.seqRight E1 (fun () => E2)`:

```anchor ClassSeqRight
class SeqRight (f : Type → Type) where
  seqRight : f α → (Unit → f β) → f β
```
There is a default implementation of `seqRight` in terms of `seq`: `seqRight (a : f α) (b : Unit → f β) : f β := pure (fun _ x => x) <*> a <*> b ()`.

Using `seqRight`, `checkCompany` becomes simpler:

```anchor checkCompanyProv2
def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  pure .company <*> checkName input.name
```
One more simplification is possible.
For every `Applicative`, `pure F <*> E` is equivalent to `f <$> E`.
In other words, using `seq` to apply a function that was placed into the `Applicative` type using `pure` is overkill, and the function could have just been applied using `Functor.map`.
This simplification yields:

```anchor checkCompany
def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  .company <$> checkName input.name
```

The remaining two constructors of `LegacyCheckedInput` use subtypes for their fields.
A general-purpose tool for checking subtypes will make these easier to read:

```anchor checkSubtype
def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }
```
In the function's argument list, it's important that the type class `[Decidable (p v)]` occur after the specification of the arguments `v` and `p`.
Otherwise, it would refer to an additional set of automatic implicit arguments, rather than to the manually-provided values.
The `Decidable` instance is what allows the proposition `p v` to be checked using {kw}`if`.

The two human cases do not need any additional tools:

```anchor checkHumanBefore1970
def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970) ("birth year", "less than 1970") <*>
      pure input.name
```

```anchor checkHumanAfter1970
def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) ("birth year", "greater than 1970") <*>
      checkName input.name
```

The validators for the three cases can be combined using `<|>`:

```anchor checkLegacyInput
def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input
```

The successful cases return constructors of `LegacyCheckedInput`, as expected:
```anchor trollGroomers
#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
```
```anchorInfo trollGroomers
Validate.ok (LegacyCheckedInput.company "Johnny's Troll Groomers")
```
```anchor johnny
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
```
```anchorInfo johnny
Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "Johnny")
```
```anchor johnnyAnon
#eval checkLegacyInput ⟨"", "1963"⟩
```
```anchorInfo johnnyAnon
Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "")
```

The worst possible input returns all the possible failures:
```anchor allFailures
#eval checkLegacyInput ⟨"", "1970"⟩
```
```anchorInfo allFailures
Validate.errors
  { head := ("birth year", "FIRM if a company"),
    tail := [("name", "Required"),
             ("birth year", "less than 1970"),
             ("birth year", "greater than 1970"),
             ("name", "Required")] }
```


# The `Alternative` Class

Many types support a notion of failure and recovery.
The `Many` monad from the section on [evaluating arithmetic expressions in a variety of monads](../monads/arithmetic.md#nondeterministic-search) is one such type, as is `Option`.
Both support failure without providing a reason (unlike, say, `Except` and `Validate`, which require some indication of what went wrong).

The `Alternative` class describes applicative functors that have additional operators for failure and recovery:

```anchor FakeAlternative
class Alternative (f : Type → Type) extends Applicative f where
  failure : f α
  orElse : f α → (Unit → f α) → f α
```
Just as implementors of `Add α` get `HAdd α α α` instances for free, implementors of `Alternative` get `OrElse` instances for free:

```anchor AltOrElse
instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse
```

The implementation of `Alternative` for `Option` keeps the first none-`none` argument:

```anchor AlternativeOption
instance : Alternative Option where
  failure := none
  orElse
    | some x, _ => some x
    | none, y => y ()
```
Similarly, the implementation for `Many` follows the general structure of `Many.union`, with minor differences due to the laziness-inducing `Unit` parameters being placed differently:

```anchor AlternativeMany
def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

instance : Alternative Many where
  failure := .none
  orElse := Many.orElse
```

Like other type classes, `Alternative` enables the definition of a variety of operations that work for _any_ applicative functor that implements `Alternative`.
One of the most important is `guard`, which causes `failure` when a decidable proposition is false:

```anchor guard
def guard [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then
    pure ()
  else failure
```
It is very useful in monadic programs to terminate execution early.
In `Many`, it can be used to filter out a whole branch of a search, as in the following program that computes all even divisors of a natural number:

```anchor evenDivisors
def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k
```
Running it on `20` yields the expected results:
```anchor evenDivisors20
#eval (evenDivisors 20).takeAll
```
```anchorInfo evenDivisors20
[20, 10, 4, 2]
```


# Exercises

## Improve Validation Friendliness

The errors returned from `Validate` programs that use `<|>` can be difficult to read, because inclusion in the list of errors simply means that the error can be reached through _some_ code path.
A more structured error report can be used to guide the user through the process more accurately:

 * Replace the `NonEmptyList` in `Validate.error` with a bare type variable, and then update the definitions of the `Applicative (Validate ε)` and `OrElse (Validate ε α)` instances to require only that there be an `Append ε` instance available.
 * Define a function `Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α` that transforms all the errors in a validation run.
 * Using the datatype `TreeError` to represent errors, rewrite the legacy validation system to track its path through the three alternatives.
 * Write a function `report : TreeError → String` that outputs a user-friendly view of the `TreeError`'s accumulated warnings and errors.


```anchor TreeError
inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both
```
