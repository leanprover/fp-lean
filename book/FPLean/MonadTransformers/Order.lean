import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Defs"

#doc (Manual) "Ordering Monad Transformers" =>
%%%
tag := "monad-transformer-order"
%%%

When composing a monad from a stack of monad transformers, it's important to be aware that the order in which the monad transformers are layered matters.
Different orderings of the same set of transformers result in different monads.

This version of {anchorName countLettersClassy}`countLetters` is just like the previous version, except it uses type classes to describe the set of available effects instead of providing a concrete monad:

```anchor countLettersClassy
def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
    (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList
```
The state and exception monad transformers can be combined in two different orders, each resulting in a monad that has instances of both type classes:

```anchor SomeMonads
abbrev M1 := StateT LetterCounts (ExceptT Err Id)
abbrev M2 := ExceptT Err (StateT LetterCounts Id)
```

When run on input for which the program does not throw an exception, both monads yield similar results:
```anchor countLettersM1Ok
#eval countLetters (m := M1) "hello" ⟨0, 0⟩
```
```anchorInfo countLettersM1Ok
Except.ok ((), { vowels := 2, consonants := 3 })
```
```anchor countLettersM2Ok
#eval countLetters (m := M2) "hello" ⟨0, 0⟩
```
```anchorInfo countLettersM2Ok
(Except.ok (), { vowels := 2, consonants := 3 })
```
However, there is a subtle difference between these return values.
In the case of {anchorName M1eval}`M1`, the outermost constructor is {anchorName MonadExceptT}`Except.ok`, and it contains a pair of the unit constructor with the final state.
In the case of {anchorName M2eval}`M2`, the outermost constructor is the pair, which contains {anchorName MonadExceptT}`Except.ok` applied only to the unit constructor.
The final state is outside of {anchorName MonadExceptT}`Except.ok`.
In both cases, the program returns the counts of vowels and consonants.

On the other hand, only one monad yields a count of vowels and consonants when the string causes an exception to be thrown.
Using {anchorName M1eval}`M1`, only an exception value is returned:
```anchor countLettersM1Error
#eval countLetters (m := M1) "hello!" ⟨0, 0⟩
```
```anchorInfo countLettersM1Error
Except.error (StEx.Err.notALetter '!')
```
Using {anchorName SomeMonads}`M2`, the exception value is paired with the state as it was at the time that the exception was thrown:
```anchor countLettersM2Error
#eval countLetters (m := M2) "hello!" ⟨0, 0⟩
```
```anchorInfo countLettersM2Error
(Except.error (StEx.Err.notALetter '!'), { vowels := 2, consonants := 3 })
```

It might be tempting to think that {anchorName SomeMonads}`M2` is superior to {anchorName SomeMonads}`M1` because it provides more information that might be useful when debugging.
The same program might compute _different_ answers in {anchorName SomeMonads}`M1` than it does in {anchorName SomeMonads}`M2`, and there's no principled reason to say that one of these answers is necessarily better than the other.
This can be seen by adding a step to the program that handles exceptions:

```anchor countWithFallback
def countWithFallback
    [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
    (str : String) : m Unit :=
  try
    countLetters str
  catch _ =>
    countLetters "Fallback"
```
This program always succeeds, but it might succeed with different results.
If no exception is thrown, then the results are the same as {anchorName countWithFallback}`countLetters`:
```anchor countWithFallbackM1Ok
#eval countWithFallback (m := M1) "hello" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM1Ok
Except.ok ((), { vowels := 2, consonants := 3 })
```
```anchor countWithFallbackM2Ok
#eval countWithFallback (m := M2) "hello" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM2Ok
(Except.ok (), { vowels := 2, consonants := 3 })
```
However, if the exception is thrown and caught, then the final states are very different.
With {anchorName countWithFallbackM1Error}`M1`, the final state contains only the letter counts from {anchorTerm countWithFallback}`"Fallback"`:
```anchor countWithFallbackM1Error
#eval countWithFallback (m := M1) "hello!" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM1Error
Except.ok ((), { vowels := 2, consonants := 6 })
```
With {anchorName countWithFallbackM2Error}`M2`, the final state contains letter counts from both {anchorTerm countWithFallbackM2Error}`"hello!"` and from {anchorTerm countWithFallback}`"Fallback"`, as one would expect in an imperative language:
```anchor countWithFallbackM2Error
#eval countWithFallback (m := M2) "hello!" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM2Error
(Except.ok (), { vowels := 4, consonants := 9 })
```

In {anchorName countWithFallbackM1Error}`M1`, throwing an exception “rolls back” the state to where the exception was caught.
In {anchorName countLettersM2Error}`M2`, modifications to the state persist across the throwing and catching of exceptions.
This difference can be seen by unfolding the definitions of {anchorName SomeMonads}`M1` and {anchorName SomeMonads}`M2`.
{anchorTerm M1eval}`M1 α` unfolds to {anchorTerm M1eval}`LetterCounts → Except Err (α × LetterCounts)`, and {anchorTerm M2eval}`M2 α` unfolds to {anchorTerm M2eval}`LetterCounts → Except Err α × LetterCounts`.
That is to say, {anchorTerm M1eval}`M1 α` describes functions that take an initial letter count, returning either an error or an {anchorName M1eval}`α` paired with updated counts.
When an exception is thrown in {anchorName M1eval}`M1`, there is no final state.
{anchorTerm M2eval}`M2 α` describes functions that take an initial letter count and return a new letter count paired with either an error or an {anchorName M2eval}`α`.
When an exception is thrown in {anchorName M2eval}`M2`, it is accompanied by a state.

# Commuting Monads
%%%
tag := "commuting-monads"
%%%

In the jargon of functional programming, two monad transformers are said to _commute_ if they can be re-ordered without the meaning of the program changing.
The fact that the result of the program can differ when {anchorName SomeMonads}`StateT` and {anchorName SomeMonads}`ExceptT` are reordered means that state and exceptions do not commute.
In general, monad transformers should not be expected to commute.

Even though not all monad transformers commute, some do.
For example, two uses of {anchorName SomeMonads}`StateT` can be re-ordered.
Expanding the definitions in {anchorTerm StateTDoubleA}`StateT σ (StateT σ' Id) α` yields the type {anchorTerm StateTDoubleA}`σ → σ' → ((α × σ) × σ')`, and {anchorTerm StateTDoubleB}`StateT σ' (StateT σ Id) α` yields {anchorTerm StateTDoubleB}`σ' → σ → ((α × σ') × σ)`.
In other words, the differences between them are that they nest the {anchorName StateTDoubleA}`σ` and {anchorName StateTDoubleA}`σ'` types in different places in the return type, and they accept their arguments in a different order.
Any client code will still need to provide the same inputs, and it will still receive the same outputs.

Most programming languages that have both mutable state and exceptions work like {anchorName SomeMonads}`M2`.
In those languages, state that _should_ be rolled back when an exception is thrown is difficult to express, and it usually needs to be simulated in a manner that looks much like the passing of explicit state values in {anchorName SomeMonads}`M1`.
Monad transformers grant the freedom to choose an interpretation of effect ordering that works for the problem at hand, with both choices being equally easy to program with.
However, they also require care to be taken in the choice of ordering of transformers.
With great expressive power comes the responsibility to check that what's being expressed is what is intended, and the type signature of {anchorName countWithFallback}`countWithFallback` is probably more polymorphic than it should be.


# Exercises
%%%
tag := "monad-transformer-order-exercises"
%%%

 * Check that {anchorName m}`ReaderT` and {anchorName SomeMonads}`StateT` commute by expanding their definitions and reasoning about the resulting types.
 * Do {anchorName m}`ReaderT` and {anchorName SomeMonads}`ExceptT` commute? Check your answer by expanding their definitions and reasoning about the resulting types.
 * Construct a monad transformer {lit}`ManyT` based on the definition of {anchorName Many (module:=Examples.Monads.Many)}`Many`, with a suitable {anchorName AlternativeOptionT}`Alternative` instance. Check that it satisfies the {anchorName AlternativeOptionT}`Monad` contract.
 * Does {lit}`ManyT` commute with {anchorName SomeMonads}`StateT`? If so, check your answer by expanding definitions and reasoning about the resulting types. If not, write a program in {lit}`ManyT (StateT σ Id)` and a program in {lit}`StateT σ (ManyT Id)`. Each program should be one that makes more sense for the given ordering of monad transformers.
