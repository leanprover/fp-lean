import VersoManual
import FPLean.Examples


open Verso.Genre Manual

open FPLean

set_option verso.exampleProject "../examples"

example_module Examples.Cat

#doc (Manual) "Additional Conveniences" =>

# Nested Actions

Many of the functions in `feline` exhibit a repetitive pattern in which an `IO` action's result is given a name, and then used immediately and only once.
For instance, in {moduleName FelineLib}`dump`:
```module FelineLib (anchor:=dump)
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```

the pattern occurs for {moduleName FelineLib (anchor:=stdoutBind)}`stdout`:
```module FelineLib (anchor:=stdoutBind)
    let stdout ← IO.getStdout
    stdout.write buf
```

Similarly, {moduleName FelineLib}`fileStream` contains the following snippet:
```module FelineLib (anchor:=fileExistsBind)
  let fileExists ← filename.pathExists
  if not fileExists then
```


When Lean is compiling a {moduleTerm FelineLib}`do` block, expressions that consist of a left arrow immediately under parentheses are lifted to the nearest enclosing {moduleTerm FelineLib}`do`, and their results are bound to a unique name.
This unique name replaces the origin of the expression.
This means that {moduleName Examples.Cat}`dump` can also be written as follows:

{exampleDecl dump}

This version of {moduleName Examples.Cat}`dump` avoids introducing names that are used only once, which can greatly simplify a program.
{moduleName Examples.Cat}`IO` actions that Lean lifts from a nested expression context are called _nested actions_.

{moduleName Examples.Cat}`fileStream` can be simplified using the same technique:

{exampleDecl fileStream}

In this case, the local name of {moduleName Examples.Cat}`handle` could also have been eliminated using nested actions, but the resulting expression would have been long and complicated.
Even though it's often good style to use nested actions, it can still sometimes be helpful to name intermediate results.

It is important to remember, however, that nested actions are only a shorter notation for {moduleName Examples.Cat}`IO` actions that occur in a surrounding {moduleTerm Examples.Cat}`do` block.
The side effects that are involved in executing them still occur in the same order, and execution of side effects is not interspersed with the evaluation of expressions.
Therefore, nested actions cannot be lifted from the branches of an {kw}`if`.

For an example of where this might be confusing, consider the following helper definitions that return data after announcing to the world that they have been executed:

{exampleDecl getNumA}

{exampleDecl getNumB}

These definitions are intended to stand in for more complicated `IO` code that might validate user input, read a database, or open a file.

A program that prints {moduleTerm Examples.Cat}`0` when number A is five, or number B otherwise, might be written as follows:

{exampleIn testEffects}

This program would be equivalent to:

{exampleDecl testEffectsExpanded}

which runs {moduleName Examples.Cat}`getNumB` regardless of whether the result of {moduleName Examples.Cat}`getNumA` is equal to {moduleTerm Examples.Cat}`5`.
To prevent this confusion, nested actions are not allowed in an {kw}`if` that is not itself a line in the {moduleTerm Examples.Cat}`do`, and the following error message results:

{exampleError testEffects}


# Flexible Layouts for `do`

In Lean, {moduleTerm Examples.Cat}`do` expressions are whitespace-sensitive.
Each {moduleName Examples.Cat}`IO` action or local binding in the {moduleTerm Examples.Cat}`do` is expected to start on its own line, and they should all have the same indentation.
Almost all uses of {moduleTerm Examples.Cat}`do` should be written this way.
In some rare contexts, however, manual control over whitespace and indentation may be necessary, or it may be convenient to have multiple small actions on a single line.
In these cases, newlines can be replaced with a semicolon and indentation can be replaced with curly braces.

For instance, all of the following programs are equivalent:

{exampleDecl helloOne}

{exampleDecl helloTwo}

{exampleDecl helloThree}


Idiomatic Lean code uses curly braces with {moduleTerm Examples.Cat}`do` very rarely.

# Running `IO` Actions With {kw}`#eval`

Lean's {moduleTerm Examples.Cat}`#eval` command can be used to execute {moduleName Examples.Cat}`IO` actions, rather than just evaluating them.
Normally, adding a {moduleTerm Examples.Cat}`#eval` command to a Lean file causes Lean to evaluate the provided expression, convert the resulting value to a string, and provide that string as a tooltip and in the info window.
Rather than failing because {moduleName Examples.Cat}`IO` actions can't be converted to strings, {moduleTerm Examples.Cat}`#eval` executes them, carrying out their side effects.
If the result of execution is the {moduleName Examples.Cat}`Unit` value {moduleTerm Examples.Cat}`()`, then no result string is shown, but if it is a type that can be converted to a string, then Lean displays the resulting value.

This means that, given the prior definitions of {moduleName Examples.HelloWorld}`countdown` and {moduleName Examples.HelloWorld}`runActions`,

{exampleIn Examples.HelloWorld evalDoesIO}

displays

{exampleInfo Examples.HelloWorld evalDoesIO}

This is the output produced by running the {moduleName Examples.HelloWorld}`IO` action, rather than some opaque representation of the action itself.
In other words, for {moduleName Examples.HelloWorld}`IO` actions, {moduleTerm Examples.HelloWorld}`#eval` both _evaluates_ the provided expression and _executes_ the resulting action value.

Quickly testing {moduleName Examples.HelloWorld}`IO` actions with {moduleTerm Examples.HelloWorld}`#eval` can be much more convenient that compiling and running whole programs.
However, there are some limitations.
For instance, reading from standard input simply returns empty input.
Additionally, the {moduleName Examples.HelloWorld}`IO` action is re-executed whenever Lean needs to update the diagnostic information that it provides to users, and this can happen at unpredictable times.
An action that reads and writes files, for instance, may do so unexpectedly.
