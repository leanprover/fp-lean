import VersoManual

import FPLean.Examples

import FPLean.MonadTransformers.ReaderIO
import FPLean.MonadTransformers.Transformers
import FPLean.MonadTransformers.Order
import FPLean.MonadTransformers.Do
import FPLean.MonadTransformers.Conveniences
import FPLean.MonadTransformers.Summary

open Verso.Genre Manual
open Verso Code External

open FPLean


set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads"

#doc (Manual) "Monad Transformers" =>

A monad is a way to encode some collection of side effects in a pure language.
Different monads provide different effects, such as state and error handling.
Many monads even provide useful effects that aren't available in most languages, such as nondeterministic searches, readers, and even continuations.

A typical application has a core set of easily testable functions written without monads paired with an outer wrapper that uses a monad to encode the necessary application logic.
These monads are constructed from well-known components.
For example:
 * Mutable state is encoded with a function parameter and a return value that have the same type
 * Error handling is encoded by having a return type that is similar to {moduleName}`Except`, with constructors for success and failure
 * Logging is encoded by pairing the return value with the log

Writing each monad by hand is tedious, however, involving boilerplate definitions of the various type classes.
Each of these components can also be extracted to a definition that modifies some other monad to add an additional effect.
Such a definition is called a _monad transformer_.
A concrete monad can be build from a collection of monad transformers, which enables much more code re-use.

{include 1 FPLean.MonadTransformers.ReaderIO}

{include 1 FPLean.MonadTransformers.Transformers}

{include 1 FPLean.MonadTransformers.Order}

{include 1 FPLean.MonadTransformers.Do}

{include 1 FPLean.MonadTransformers.Conveniences}

{include 1 FPLean.MonadTransformers.Summary}
