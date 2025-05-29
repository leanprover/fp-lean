import VersoManual
import FPLean.Examples

import FPLean.DependentTypes.IndexedFamilies
import FPLean.DependentTypes.UniversePattern
import FPLean.DependentTypes.TypedQueries
import FPLean.DependentTypes.IndicesParametersUniverses
import FPLean.DependentTypes.Pitfalls
import FPLean.DependentTypes.Summary

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes"

#doc (Manual) "Programming with Dependent Types" =>

In most statically-typed programming languages, there is a hermetic seal between the world of types and the world of programs.
Types and programs have different grammars and they are used at different times.
Types are typically used at compile time, to check that a program obeys certain invariants.
Programs are used at run time, to actually perform computations.
When the two interact, it is usually in the form of a type-case operator like an “instance-of” check or a casting operator that provides the type checker with information that was otherwise unavailable, to be verified at run time.
In other words, the interaction consists of types being inserted into the world of programs, where they gain some limited run-time meaning.

Lean does not impose this strict separation.
In Lean, programs may compute types and types may contain programs.
Placing programs in types allows their full computational power to be used at compile time, and the ability to return types from functions makes types into first-class participants in the programming process.

_Dependent types_ are types that contain non-type expressions.
A common source of dependent types is a named argument to a function.
For example, the function {anchorName natOrStringThree}`natOrStringThree` returns either a natural number or a string, depending on which {anchorName natOrStringThree}`Bool` it is passed:

```anchor natOrStringThree
def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"
```

Further examples of dependent types include:
 * {ref "polymorphism"}[The introductory section on polymorphism] contains {anchorName posOrNegThree (module:= Examples.Intro)}`posOrNegThree`, in which the function's return type depends on the value of the argument.
 * {ref "literal-numbers"}[The {anchorName OfNat (module := Examples.Classes)}`OfNat` type class] depends on the specific natural number literal being used.
 * {ref "validated-input"}[The {anchorName CheckedInput (module := Examples.FunctorApplicativeMonad)}`CheckedInput` structure] used in the example of validators depends on the year in which validation occurred.
 * {ref "subtypes"}[Subtypes] contain propositions that refer to particular values.
 * Essentially all interesting propositions, including those that determine the validity of {ref "props-proofs-indexing"}[array indexing notation], are types that contain values and are thus dependent types.

Dependent types vastly increase the power of a type system.
The flexibility of return types that branch on argument values enables programs to be written that cannot easily be given types in other type systems.
At the same time, dependent types allow a type signature to restrict which values may be returned from a function, enabling strong invariants to be enforced at compile time.

However, programming with dependent types can be quite complex, and it requires a whole set of skills above and beyond functional programming.
Expressive specifications can be complicated to fulfill, and there is a real risk of tying oneself in knots and being unable to complete the program.
On the other hand, this process can lead to new understanding, which can be expressed in a refined type that can be fulfilled.
While this chapter scratches the surface of dependently typed programming, it is a deep topic that deserves an entire book of its own.

{include 1 FPLean.DependentTypes.IndexedFamilies}

{include 1 FPLean.DependentTypes.UniversePattern}

{include 1 FPLean.DependentTypes.TypedQueries}

{include 1 FPLean.DependentTypes.IndicesParametersUniverses}

{include 1 FPLean.DependentTypes.Pitfalls}

{include 1 FPLean.DependentTypes.Summary}
