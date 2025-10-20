import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "FelineLib"


#doc (Manual) "Additional Conveniences" =>
%%%
tag := "hello-world-conveniences"
%%%

# Nested Actions
%%%
tag := "nested-actions"
%%%

:::paragraph
Many of the functions in {lit}`feline` exhibit a repetitive pattern in which an {anchorName dump}`IO` action's result is given a name, and then used immediately and only once.
For instance, in {moduleName}`dump`:
```anchor dump
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```

the pattern occurs for {moduleName (anchor:=stdoutBind)}`stdout`:
```anchor stdoutBind
    let stdout ← IO.getStdout
    stdout.write buf
```

Similarly, {moduleName}`fileStream` contains the following snippet:
```anchor fileExistsBind
  let fileExists ← filename.pathExists
  if not fileExists then
```
:::

:::paragraph
When Lean is compiling a {moduleTerm}`do` block, expressions that consist of a left arrow immediately under parentheses are lifted to the nearest enclosing {moduleTerm}`do`, and their results are bound to a unique name.
This unique name replaces the origin of the expression.
This means that {moduleName (module := Examples.Cat)}`dump` can also be written as follows:

```anchor dump (module:=Examples.Cat)
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream
```

This version of {anchorName dump (module := Examples.Cat)}`dump` avoids introducing names that are used only once, which can greatly simplify a program.
{moduleName (module := Examples.Cat)}`IO` actions that Lean lifts from a nested expression context are called _nested actions_.
:::

:::paragraph
{moduleName (module := Examples.Cat)}`fileStream` can be simplified using the same technique:

```anchor fileStream (module := Examples.Cat)
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))
```

In this case, the local name of {anchorName fileStream (module := Examples.Cat)}`handle` could also have been eliminated using nested actions, but the resulting expression would have been long and complicated.
Even though it's often good style to use nested actions, it can still sometimes be helpful to name intermediate results.
:::

It is important to remember, however, that nested actions are only a shorter notation for {moduleName (module := Examples.Cat)}`IO` actions that occur in a surrounding {moduleTerm (module := Examples.Cat)}`do` block.
The side effects that are involved in executing them still occur in the same order, and execution of side effects is not interspersed with the evaluation of expressions.
Therefore, nested actions cannot be lifted from the branches of an {kw}`if`.

For an example of where this might be confusing, consider the following helper definitions that return data after announcing to the world that they have been executed:

```anchor getNumA (module := Examples.Cat)
def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5
```

```anchor getNumB (module := Examples.Cat)
def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 7
```

These definitions are intended to stand in for more complicated {anchorName getNumB (module:=Examples.Cat)}`IO` code that might validate user input, read a database, or open a file.

A program that prints {moduleTerm (module := Examples.Cat)}`0` when number A is five, or number B otherwise, might be written as follows:

```anchor testEffects (module := Examples.Cat)
def test : IO Unit := do
  let a : Nat := if (← getNumA) == 5 then 0 else (← getNumB)
  (← IO.getStdout).putStrLn s!"The answer is {a}"
```

This program would be equivalent to:

```anchor testEffectsExpanded (module := Examples.Cat)
def test : IO Unit := do
  let x ← getNumA
  let y ← getNumB
  let a : Nat := if x == 5 then 0 else y
  (← IO.getStdout).putStrLn s!"The answer is {a}"
```

which runs {moduleName (module := Examples.Cat)}`getNumB` regardless of whether the result of {moduleName (module := Examples.Cat)}`getNumA` is equal to {moduleTerm (module := Examples.Cat)}`5`.
To prevent this confusion, nested actions are not allowed in an {kw}`if` that is not itself a line in the {moduleTerm (module := Examples.Cat)}`do`, and the following error message results:

```anchorError testEffects (module := Examples.Cat)
invalid use of `(<- ...)`, must be nested inside a 'do' expression
```


# Flexible Layouts for {lit}`do`
%%%
tag := "do-layout-syntax"
%%%

In Lean, {moduleTerm (module := Examples.Cat)}`do` expressions are whitespace-sensitive.
Each {moduleName (module := Examples.Cat)}`IO` action or local binding in the {moduleTerm (module := Examples.Cat)}`do` is expected to start on its own line, and they should all have the same indentation.
Almost all uses of {moduleTerm (module := Examples.Cat)}`do` should be written this way.
In some rare contexts, however, manual control over whitespace and indentation may be necessary, or it may be convenient to have multiple small actions on a single line.
In these cases, newlines can be replaced with a semicolon and indentation can be replaced with curly braces.

For instance, all of the following programs are equivalent:

```anchor helloOne (module := Examples.Cat)
-- This version uses only whitespace-sensitive layout
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trim
  stdout.putStrLn s!"Hello, {name}!"
```

```anchor helloTwo (module := Examples.Cat)
-- This version is as explicit as possible
def main : IO Unit := do {
  let stdin ← IO.getStdin;
  let stdout ← IO.getStdout;

  stdout.putStrLn "How would you like to be addressed?";
  let name := (← stdin.getLine).trim;
  stdout.putStrLn s!"Hello, {name}!"
}
```

```anchor helloThree (module := Examples.Cat)
-- This version uses a semicolon to put two actions on the same line
def main : IO Unit := do
  let stdin ← IO.getStdin; let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trim
  stdout.putStrLn s!"Hello, {name}!"
```


Idiomatic Lean code uses curly braces with {moduleTerm (module := Examples.Cat)}`do` very rarely.

# Running {lit}`IO` Actions With {kw}`#eval`
%%%
tag := "eval-io"
%%%

Lean's {moduleTerm (module := Examples.Cat)}`#eval` command can be used to execute {moduleName (module := Examples.Cat)}`IO` actions, rather than just evaluating them.
Normally, adding a {moduleTerm (module := Examples.Cat)}`#eval` command to a Lean file causes Lean to evaluate the provided expression, convert the resulting value to a string, and provide that string as a tooltip and in the info window.
Rather than failing because {moduleName (module := Examples.Cat)}`IO` actions can't be converted to strings, {moduleTerm (module := Examples.Cat)}`#eval` executes them, carrying out their side effects.
If the result of execution is the {moduleName (module := Examples.Cat)}`Unit` value {moduleTerm (module := Examples.Cat)}`()`, then no result string is shown, but if it is a type that can be converted to a string, then Lean displays the resulting value.

:::paragraph
This means that, given the prior definitions of {moduleName (module := Examples.HelloWorld)}`countdown` and {moduleName (module := Examples.HelloWorld)}`runActions`,

```anchor evalDoesIO (module := Examples.HelloWorld)
#eval runActions (countdown 3)
```

displays

```anchorInfo evalDoesIO (module := Examples.HelloWorld)
3
2
1
Blast off!
```
:::

This is the output produced by running the {moduleName (module := Examples.HelloWorld)}`IO` action, rather than some opaque representation of the action itself.
In other words, for {moduleName (module := Examples.HelloWorld)}`IO` actions, {moduleTerm (module := Examples.HelloWorld)}`#eval` both _evaluates_ the provided expression and _executes_ the resulting action value.

Quickly testing {moduleName (module := Examples.HelloWorld)}`IO` actions with {moduleTerm (module := Examples.HelloWorld)}`#eval` can be much more convenient that compiling and running whole programs.
However, there are some limitations.
For instance, reading from standard input simply returns empty input.
Additionally, the {moduleName (module := Examples.HelloWorld)}`IO` action is re-executed whenever Lean needs to update the diagnostic information that it provides to users, and this can happen at unpredictable times.
An action that reads and writes files, for instance, may do so unexpectedly.
