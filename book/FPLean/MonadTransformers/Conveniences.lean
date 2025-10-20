import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Conveniences"

#doc (Manual) "Additional Conveniences" =>
%%%
tag := "monad-transformer-conveniences"
%%%

# Pipe Operators
%%%
tag := "pipe-operators"
%%%

Functions are normally written before their arguments.
When reading a program from left to right, this promotes a view in which the function's _output_ is paramount—the function has a goal to achieve (that is, a value to compute), and it receives arguments to support it in this process.
But some programs are easier to understand in terms of an input that is successively refined to produce the output.
For these situations, Lean provides a _pipeline_ operator which is similar to the that provided by F#.
Pipeline operators are useful in the same situations as Clojure's threading macros.

The pipeline {anchorTerm pipelineShort}`E₁ |> E₂` is short for {anchorTerm pipelineShort}`E₂ E₁`.
For example, evaluating:
```anchor some5
#eval some 5 |> toString
```
results in:
```anchorInfo some5
"(some 5)"
```
While this change of emphasis can make some programs more convenient to read, pipelines really come into their own when they contain many components.

With the definition:

```anchor times3
def times3 (n : Nat) : Nat := n * 3
```
the following pipeline:
```anchor itIsFive
#eval 5 |> times3 |> toString |> ("It is " ++ ·)
```
yields:
```anchorInfo itIsFive
"It is 15"
```
More generally, a series of pipelines {anchorTerm pipeline}`E₁ |> E₂ |> E₃ |> E₄` is short for nested function applications {anchorTerm pipeline}`E₄ (E₃ (E₂ E₁))`.

Pipelines may also be written in reverse.
In this case, they do not place the subject of data transformation first; however, in cases where many nested parentheses pose a challenge for readers, they can clarify the steps of application.
The prior example could be equivalently written as:
```anchor itIsAlsoFive
#eval ("It is " ++ ·) <| toString <| times3 <| 5
```
which is short for:
```anchor itIsAlsoFiveParens
#eval ("It is " ++ ·) (toString (times3 5))
```

Lean's method dot notation that uses the name of the type before the dot to resolve the namespace of the operator after the dot serves a similar purpose to pipelines.
Even without the pipeline operator, it is possible to write {anchorTerm listReverse}`[1, 2, 3].reverse` instead of {anchorTerm listReverse}`List.reverse [1, 2, 3]`.
However, the pipeline operator is also useful for dotted functions when using many of them.
{anchorTerm listReverseDropReverse}`([1, 2, 3].reverse.drop 1).reverse` can also be written as {anchorTerm listReverseDropReverse}`[1, 2, 3] |> List.reverse |> List.drop 1 |> List.reverse`.
This version avoids having to parenthesize expressions simply because they accept arguments, and it recovers the convenience of a chain of method calls in languages like Kotlin or C#.
However, it still requires the namespace to be provided by hand.
As a final convenience, Lean provides the “pipeline dot” operator, which groups functions like the pipeline but uses the name of the type to resolve namespaces.
With “pipeline dot”, the example can be rewritten to {anchorTerm listReverseDropReversePipe}`[1, 2, 3] |>.reverse |>.drop 1 |>.reverse`.

# Infinite Loops
%%%
tag := "infinite-loops"
%%%

Within a {kw}`do`-block, the {kw}`repeat` keyword introduces an infinite loop.
For example, a program that spams the string {anchorTerm spam}`"Spam!"` can use it:

```anchor spam
def spam : IO Unit := do
  repeat IO.println "Spam!"
```
A {kw}`repeat` loop supports {kw}`break` and {kw}`continue`, just like {kw}`for` loops.

The {anchorName dump (module := FelineLib)}`dump` function from the {ref "streams"}[implementation of {lit}`feline`] uses a recursive function to run forever:
```anchor dump (module := FelineLib)
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```
This function can be greatly shortened using {kw}`repeat`:

```anchor dump
def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  repeat do
    let buf ← stream.read bufsize
    if buf.isEmpty then break
    stdout.write buf
```

Neither {anchorName spam}`spam` nor {anchorName dump}`dump` need to be declared as {kw}`partial` because they are not themselves infinitely recursive.
Instead, {kw}`repeat` makes use of a type whose {anchorTerm names}`ForM` instance is {kw}`partial`.
Partiality does not “infect” calling functions.

# While Loops
%%%
tag := "while-loops"
%%%

When programming with local mutability, {kw}`while` loops can be a convenient alternative to {kw}`repeat` with an {kw}`if`-guarded {kw}`break`:

```anchor dumpWhile
def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  let mut buf ← stream.read bufsize
  while not buf.isEmpty do
    stdout.write buf
    buf ← stream.read bufsize
```
Behind the scenes, {kw}`while` is just a simpler notation for {kw}`repeat`.
