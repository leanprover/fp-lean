import VersoManual
import FPLean.Examples


open Verso.Genre Manual ExternalLean

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "HelloName"

example_module Examples.HelloWorld



#doc (Manual) "Step By Step" =>

:::paragraph
A {moduleTerm}`do` block can be executed one line at a time.
Start with the program from the prior section:

```anchor block1
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"
```
:::

# Standard IO

:::paragraph
The first line is {anchor line1}`let stdin ← IO.getStdin`, while the remainder is:
```anchor block2
  let stdout ← IO.getStdout
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"
```
:::

To execute a {kw}`let` statement that uses a `←`, start by evaluating the expression to the right of the arrow (in this case, {moduleTerm}`IO.getStdin`).
Because this expression is just a variable, its value is looked up.
The resulting value is a built-in primitive {moduleTerm}`IO` action.
The next step is to execute this {moduleTerm}`IO` action, resulting in a value that represents the standard input stream, which has type {moduleTerm}`IO.FS.Stream`.
Standard input is then associated with the name to the left of the arrow (here {anchorTerm line1}`stdin`) for the remainder of the {moduleTerm}`do` block.

Executing the second line, {anchor line2}`let stdout ← IO.getStdout`, proceeds similarly.
First, the expression {moduleTerm}`IO.getStdout` is evaluated, yielding an {moduleTerm}`IO` action that will return the standard output.
Next, this action is executed, actually returning the standard output.
Finally, this value is associated with the name {anchorTerm line2}`stdout` for the remainder of the {moduleTerm}`do` block.

# Asking a Question

:::paragraph
Now that {anchorTerm line1}`stdin` and {anchorTerm line2}`stdout` have been found, the remainder of the block consists of a question and an answer:
```anchor block3
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"
```
:::

The first statement in the block, {anchor line3}`stdout.putStrLn "How would you like to be addressed?"`, consists of an expression.
To execute an expression, it is first evaluated.
In this case, {moduleTerm}`IO.FS.Stream.putStrLn` has type {moduleTerm}`IO.FS.Stream → String → IO Unit`.
This means that it is a function that accepts a stream and a string, returning an {moduleTerm}`IO` action.
The expression uses [accessor notation](../getting-to-know/structures.md#behind-the-scenes) for a function call.
This function is applied to two arguments: the standard output stream and a string.
The value of the expression is an {moduleTerm}`IO` action that will write the string and a newline character to the output stream.
Having found this value, the next step is to execute it, which causes the string and newline to actually be written to {anchorTerm setup}`stdout`.
Statements that consist only of expressions do not introduce any new variables.

The next statement in the block is {anchor line4}`let input ← stdin.getLine`.
{moduleTerm}`IO.FS.Stream.getLine` has type {moduleTerm}`IO.FS.Stream → IO String`, which means that it is a function from a stream to an {moduleTerm}`IO` action that will return a string.
Once again, this is an example of accessor notation.
This {moduleTerm}`IO` action is executed, and the program waits until the user has typed a complete line of input.
Assume the user writes "`David`".
The resulting line (`"David\n"`) is associated with {anchorTerm block5}`input`, where the escape sequence `\n` denotes the newline character.

```anchor block5
  let name := input.dropRightWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"
```

:::paragraph
The next line, {anchor line5}`let name := input.dropRightWhile Char.isWhitespace`, is a {kw}`let` statement.
Unlike the other {kw}`let` statements in this program, it uses `:=` instead of `←`.
This means that the expression will be evaluated, but the resulting value need not be an {moduleTerm}`IO` action and will not be executed.
In this case, {moduleTerm}`String.dropRightWhile` takes a string and a predicate over characters and returns a new string from which all the characters at the end of the string that satisfy the predicate have been removed.
For example,

{exampleIn dropBang}

yields

{exampleInfo dropBang}

and

{exampleIn dropNonLetter}

yields

{exampleInfo dropNonLetter}

in which all non-alphanumeric characters have been removed from the right side of the string.
In the current line of the program, whitespace characters (including the newline) are removed from the right side of the input string, resulting in {moduleTerm (module := Examples.HelloWorld)}`"David"`, which is associated with {anchorTerm block5}`name` for the remainder of the block.
:::

# Greeting the User

:::paragraph
All that remains to be executed in the {moduleTerm}`do` block is a single statement:
```anchor line6
  stdout.putStrLn s!"Hello, {name}!"
```
:::

The string argument to {anchorTerm line6}`putStrLn` is constructed via string interpolation, yielding the string {moduleTerm (module := Examples.HelloWorld)}`"Hello, David!"`.
Because this statement is an expression, it is evaluated to yield an {moduleTerm}`IO` action that will print this string with a newline to standard output.
Once the expression has been evaluated, the resulting {moduleTerm}`IO` action is executed, resulting in the greeting.

# `IO` Actions as Values

In the above description, it can be difficult to see why the distinction between evaluating expressions and executing {moduleTerm}`IO` actions is necessary.
After all, each action is executed immediately after it is produced.
Why not simply carry out the effects during evaluation, as is done in other languages?

The answer is twofold.
First off, separating evaluation from execution means that programs must be explicit about which functions can have side effects.
Because the parts of the program that do not have effects are much more amenable to mathematical reasoning, whether in the heads of programmers or using Lean's facilities for formal proof, this separation can make it easier to avoid bugs.
Secondly, not all {moduleTerm}`IO` actions need be executed at the time that they come into existence.
The ability to mention an action without carrying it out allows ordinary functions to be used as control structures.

:::paragraph
For example, the function {term}`twice.name` takes an {moduleTerm}`IO` action as its argument, returning a new action that will execute the argument action twice.

{exampleDecl twice}

Executing

```exampleIn twiceShy
twice (IO.println "shy")
```

results in

```exampleInfo twiceShy
shy
shy
```

being printed.
This can be generalized to a version that runs the underlying action any number of times:

```exampleDecl nTimes
def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n
```
:::

:::paragraph
In the base case for {moduleTerm (module := Examples.HelloWorld)}`Nat.zero`, the result is {moduleTerm (module := Examples.HelloWorld)}`pure ()`.
The function {moduleTerm (module := Examples.HelloWorld)}`pure` creates an {moduleTerm (module := Examples.HelloWorld)}`IO` action that has no side effects, but returns {moduleTerm (module := Examples.HelloWorld)}`pure`'s argument, which in this case is the constructor for {moduleTerm (module := Examples.HelloWorld)}`Unit`.
As an action that does nothing and returns nothing interesting, {moduleTerm (module := Examples.HelloWorld)}`pure ()` is at the same time utterly boring and very useful.
In the recursive step, a {moduleTerm (module := Examples.HelloWorld)}`do` block is used to create an action that first executes {moduleTerm (module := Examples.HelloWorld)}`action` and then executes the result of the recursive call.
Executing {exampleIn}`nTimes3` causes the following output:

{exampleInfo nTimes3}

:::

:::paragraph
In addition to using functions as control structures, the fact that {moduleTerm (module := Examples.HelloWorld)}`IO` actions are first-class values means that they can be saved in data structures for later execution.
For instance, the function {moduleName (module := Examples.HelloWorld)}`countdown` takes a {moduleTerm (module := Examples.HelloWorld)}`Nat` and returns a list of unexecuted {moduleTerm (module := Examples.HelloWorld)}`IO` actions, one for each {moduleTerm (module := Examples.HelloWorld)}`Nat`:

{exampleDecl countdown}

This function has no side effects, and does not print anything.
For example, it can be applied to an argument, and the length of the resulting list of actions can be checked:

{exampleDecl from5}

This list contains six elements (one for each number, plus a {moduleTerm (module := Examples.HelloWorld)}`"Blast off!"` action for zero):

{exampleIn from5length}

{exampleInfo from5length}

:::

:::paragraph
The function {moduleTerm (module := Examples.HelloWorld)}`runActions` takes a list of actions and constructs a single action that runs them all in order:

{exampleDecl runActions}

Its structure is essentially the same as that of {moduleName (module := Examples.HelloWorld)}`nTimes`, except instead of having one action that is executed for each {moduleName (module := Examples.HelloWorld)}`Nat.succ`, the action under each {moduleName (module := Examples.HelloWorld)}`List.cons` is to be executed.
Similarly, {moduleName (module := Examples.HelloWorld)}`runActions` does not itself run the actions.
It creates a new action that will run them, and that action must be placed in a position where it will be executed as a part of {moduleName (module := Examples.HelloWorld)}`main`:

{exampleDecl main}

Running this program results in the following output:

{exampleInfo countdown5}

:::

:::paragraph
What happens when this program is run?
The first step is to evaluate {moduleName (module := Examples.HelloWorld)}`main`. That occurs as follows:

{exampleEval evalMain}

The resulting {moduleTerm (module := Examples.HelloWorld)}`IO` action is a {moduleTerm (module := Examples.HelloWorld)}`do` block.
Each step of the {moduleTerm (module := Examples.HelloWorld)}`do` block is then executed, one at a time, yielding the expected output.
The final step, {moduleTerm (module := Examples.HelloWorld)}`pure ()`, does not have any effects, and it is only present because the definition of {moduleTerm (module := Examples.HelloWorld)}`runActions` needs a base case.
:::

# Exercise

:::paragraph
Step through the execution of the following program on a piece of paper:

{exampleDecl ExMain}

While stepping through the program's execution, identify when an expression is being evaluated and when an {moduleTerm (module := Examples.HelloWorld)}`IO` action is being executed.
When executing an {moduleTerm (module := Examples.HelloWorld)}`IO` action results in a side effect, write it down.
After doing this, run the program with Lean and double-check that your predictions about the side effects were correct.
:::
