import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers"

#doc (Manual) "Summary" =>
%%%
tag := "monad-transformer-summary"
%%%

# Combining Monads
%%%
tag := none
%%%

When writing a monad from scratch, there are design patterns that tend to describe the ways that each effect is added to the monad.
Reader effects are added by having the monad's type be a function from the reader's environment, state effects are added by including a function from the initial state to the value paired with the final state, failure or exceptions are added by including a sum type in the return type, and logging or other output is added by including a product type in the return type.
Existing monads can be made part of the return type as well, allowing their effects to be included in the new monad.

These design patterns are made into a library of reusable software components by defining _monad transformers_, which add an effect to some base monad.
Monad transformers take the simpler monad types as arguments, returning the enhanced monad types.
At a minimum, a monad transformer should provide the following instances:
 1. A {anchorName Summary}`Monad` instance that assumes the inner type is already a monad
 2. A {anchorName Summary}`MonadLift` instance to translate an action from the inner monad to the transformed monad

Monad transformers may be implemented as polymorphic structures or inductive datatypes, but they are most often implemented as functions from the underlying monad type to the enhanced monad type.

# Type Classes for Effects
%%%
tag := none
%%%

A common design pattern is to implement a particular effect by defining a monad that has the effect, a monad transformer that adds it to another monad, and a type class that provides a generic interface to the effect.
This allows programs to be written that merely specify which effects they need, so the caller can provide any monad that has the right effects.

Sometimes, auxiliary type information (e.g. the state's type in a monad that provides state, or the exception's type in a monad that provides exceptions) is an output parameter, and sometimes it is not.
The output parameter is most useful for simple programs that use each kind of effect only once, but it risks having the type checker commit to a the wrong type too early when multiple instances of the same effect are used in a given program.
Thus, both versions are typically provided, with the ordinary-parameter version of the type class having a name that ends in {lit}`-Of`.

# Monad Transformers Don't Commute
%%%
tag := none
%%%

It is important to note that changing the order of transformers in a monad can change the meaning of programs that use the monad.
For instance, re-ordering {anchorName Summary}`StateT` and {anchorTerm Summary}`ExceptT` can result either in programs that lose state modifications when exceptions are thrown or programs that keep changes.
While most imperative languages provide only the latter, the increased flexibility provided by monad transformers demands thought and attention to choose the correct variety for the task at hand.

# {kw}`do`-Notation for Monad Transformers
%%%
tag := none
%%%

Lean's {kw}`do`-blocks support early return, in which the block is terminated with some value, locally mutable variables, {kw}`for`-loops with {kw}`break` and {kw}`continue`, and single-branched {kw}`if`-statements.
While this may seem to be introducing imperative features that would get in the way of using Lean to write proofs, it is in fact nothing more than a more convenient syntax for certain common uses of monad transformers.
Behind the scenes, whatever monad the {kw}`do`-block is written in is transformed by appropriate uses of {anchorName Summary}`ExceptT` and {anchorName Summary}`StateT` to support these additional effects.
