import VersoManual
import FPLean.Examples
import FPLean.FunctorApplicativeMonad.Inheritance
import FPLean.FunctorApplicativeMonad.Applicative
import FPLean.FunctorApplicativeMonad.ApplicativeContract
import FPLean.FunctorApplicativeMonad.Alternative
import FPLean.FunctorApplicativeMonad.Universes
import FPLean.FunctorApplicativeMonad.Complete
import FPLean.FunctorApplicativeMonad.Summary


open Verso.Genre Manual ExternalLean

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.TODO"

#doc (Manual) "Functors, Applicative Functors, and Monads" =>

`Functor` and `Monad` both describe operations for types that are still waiting for a type argument.
One way to understand them is that `Functor` describes containers in which the contained data can be transformed, and `Monad` describes an encoding of programs with side effects.
This understanding is incomplete, however.
After all, `Option` has instances for both `Functor` and `Monad`, and simultaneously represents an optional value _and_ a computation that might fail to return a value.

From the perspective of data structures, `Option` is a bit like a nullable type or like a list that can contain at most one entry.
From the perspective of control structures, `Option` represents a computation that might terminate early without a result.
Typically, programs that use the `Functor` instance are easiest to think of as using `Option` as a data structure, while programs that use the `Monad` instance are easiest to think of as using `Option` to allow early failure, but learning to use both of these perspectives fluently is an important part of becoming proficient at functional programming.

There is a deeper relationship between functors and monads.
It turns out that _every monad is a functor_.
Another way to say this is that the monad abstraction is more powerful than the functor abstraction, because not every functor is a monad.
Furthermore, there is an additional intermediate abstraction, called _applicative functors_, that has enough power to write many interesting programs and yet permits libraries that cannot use the `Monad` interface.
The type class `Applicative` provides the overloadable operations of applicative functors.
Every monad is an applicative functor, and every applicative functor is a functor, but the converses do not hold.

{include 1 FPLean.FunctorApplicativeMonad.Inheritance}

{include 1 FPLean.FunctorApplicativeMonad.Applicative}

{include 1 FPLean.FunctorApplicativeMonad.ApplicativeContract}

{include 1 FPLean.FunctorApplicativeMonad.Alternative}

{include 1 FPLean.FunctorApplicativeMonad.Universes}

{include 1 FPLean.FunctorApplicativeMonad.Complete}

{include 1 FPLean.FunctorApplicativeMonad.Summary}
