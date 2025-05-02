import VersoManual
import FPLean.Examples


open Verso.Genre Manual

open FPLean

set_option verso.exampleProject "../examples"

example_module Hello

#doc (Manual) "Running a Program" =>


:::paragraph
The simplest way to run a Lean program is to use the `--run` option to the Lean executable.
Create a file called `Hello.lean` and enter the following contents:

````module Hello
def main : IO Unit := IO.println "Hello, world!"
````
:::

:::paragraph
Then, from the command line, run:

{command hello "simple-hello" "lean --run Hello.lean"}

The program displays {commandOut hello}`lean --run Hello.lean` and exits.
:::



# Anatomy of a Greeting

When Lean is invoked with the `--run` option, it invokes the program's `main` definition.
In programs that do not take command-line arguments, {moduleName Hello}`main` should have type {moduleTerm Hello}`IO Unit`.
This means that {moduleName Hello}`main` is not a function, because there are no arrows (`→`) in its type.
Instead of being a function that has side effects, {moduleTerm HelloName}`main` consists of a description of effects to be carried out.

As discussed in [the preceding chapter](../getting-to-know/polymorphism.md), {moduleTerm HelloName}`Unit` is the simplest inductive type.
It has a single constructor called {moduleTerm HelloName}`unit` that takes no arguments.
Languages in the C tradition have a notion of a {CSharp}`void` function that does not return any value at all.
In Lean, all functions take an argument and return a value, and the lack of interesting arguments or return values can be signaled by using the {moduleTerm HelloName}`Unit` type instead.
If {moduleTerm HelloName}`Bool` represents a single bit of information, {moduleTerm HelloName}`Unit` represents zero bits of information.

{moduleTerm HelloName}`IO α` is the type of a program that, when executed, will either throw an exception or return a value of type {moduleTerm HelloName}`α`.
During execution, this program may have side effects.
These programs are referred to as {moduleTerm HelloName}`IO` _actions_.
Lean distinguishes between _evaluation_ of expressions, which strictly adheres to the mathematical model of substitution of values for variables and reduction of sub-expressions without side effects, and _execution_ of `IO` actions, which rely on an external system to interact with the world.
{moduleTerm HelloName}`IO.println` is a function from strings to {moduleTerm HelloName}`IO` actions that, when executed, write the given string to standard output.
Because this action doesn't read any interesting information from the environment in the process of emitting the string, {moduleTerm HelloName}`IO.println` has type {moduleTerm HelloName}`String → IO Unit`.
If it did return something interesting, then that would be indicated by the {moduleTerm HelloName}`IO` action having a type other than {moduleTerm HelloName}`Unit`.



# Functional Programming vs Effects

Lean's model of computation is based on the evaluation of mathematical expressions, in which variables are given exactly one value that does not change over time.
The result of evaluating an expression does not change, and evaluating the same expression again will always yield the same result.

On the other hand, useful programs must interact with the world.
A program that performs neither input nor output can't ask a user for data, create files on disk, or open network connections.
Lean is written in itself, and the Lean compiler certainly reads files, creates files, and interacts with text editors.
How can a language in which the same expression always yields the same result support programs that read files from disk, when the contents of these files might change over time?

This apparent contradiction can be resolved by thinking a bit differently about side effects.
Imagine a café that sells coffee and sandwiches.
This café has two employees: a cook who fulfills orders, and a worker at the counter who interacts with customers and places order slips.
The cook is a surly person, who really prefers not to have any contact with the world outside, but who is very good at consistently delivering the food and drinks that the café is known for.
In order to do this, however, the cook needs peace and quiet, and can't be disturbed with conversation.
The counter worker is friendly, but completely incompetent in the kitchen.
Customers interact with the counter worker, who delegates all actual cooking to the cook.
If the cook has a question for a customer, such as clarifying an allergy, they send a little note to the counter worker, who interacts with the customer and passes a note back to the cook with the result.

In this analogy, the cook is the Lean language.
When provided with an order, the cook faithfully and consistently delivers what is requested.
The counter worker is the surrounding run-time system that interacts with the world and can accept payments, dispense food, and have conversations with customers.
Working together, the two employees serve all the functions of the restaurant, but their responsibilities are divided, with each performing the tasks that they're best at.
Just as keeping customers away allows the cook to focus on making truly excellent coffee and sandwiches, Lean's lack of side effects allows programs to be used as part of formal mathematical proofs.
It also helps programmers understand the parts of the program in isolation from each other, because there are no hidden state changes that create subtle coupling between components.
The cook's notes represent {moduleTerm HelloName}`IO` actions that are produced by evaluating Lean expressions, and the counter worker's replies are the values that are passed back from effects.

This model of side effects is quite similar to how the overall aggregate of the Lean language, its compiler, and its run-time system (RTS) work.
Primitives in the run-time system, written in C, implement all the basic effects.
When running a program, the RTS invokes the {moduleTerm HelloName}`main` action, which returns new {moduleTerm HelloName}`IO` actions to the RTS for execution.
The RTS executes these actions, delegating to the user's Lean code to carry out computations.
From the internal perspective of Lean, programs are free of side effects, and {moduleTerm HelloName}`IO` actions are just descriptions of tasks to be carried out.
From the external perspective of the program's user, there is a layer of side effects that create an interface to the program's core logic.


# Real-World Functional Programming

The other useful way to think about side effects in Lean is by considering {moduleTerm HelloName}`IO` actions to be functions that take the entire world as an argument and return a value paired with a new world.
In this case, reading a line of text from standard input _is_ a pure function, because a different world is provided as an argument each time.
Writing a line of text to standard output is a pure function, because the world that the function returns is different from the one that it began with.
Programs do need to be careful to never re-use the world, nor to fail to return a new world—this would amount to time travel or the end of the world, after all.
Careful abstraction boundaries can make this style of programming safe.
If every primitive {moduleTerm HelloName}`IO` action accepts one world and returns a new one, and they can only be combined with tools that preserve this invariant, then the problem cannot occur.

This model cannot be implemented.
After all, the entire universe cannot be turned into a Lean value and placed into memory.
However, it is possible to implement a variation of this model with an abstract token that stands for the world.
When the program is started, it is provided with a world token.
This token is then passed on to the IO primitives, and their returned tokens are similarly passed to the next step.
At the end of the program, the token is returned to the operating system.

This model of side effects is a good description of how {moduleTerm HelloName}`IO` actions as descriptions of tasks to be carried out by the RTS are represented internally in Lean.
The actual functions that transform the real world are behind an abstraction barrier.
But real programs typically consist of a sequence of effects, rather than just one.
To enable programs to use multiple effects, there is a sub-language of Lean called `do` notation that allows these primitive {moduleTerm HelloName}`IO` actions to be safely composed into a larger, useful program.

# Combining `IO` Actions

Most useful programs accept input in addition to producing output.
Furthermore, they may take decisions based on input, using the input data as part of a computation.
The following program, called `HelloName.lean`, asks the user for their name and then greets them:

```module HelloName (anchor:=all)
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"
```



In this program, the `main` action consists of a `do` block.
This block contains a sequence of _statements_, which can be both local variables (introduced using `let`) and actions that are to be executed.
Just as SQL can be thought of as a special-purpose language for interacting with databases, the `do` syntax can be thought of as a special-purpose sub-language within Lean that is dedicated to modeling imperative programs.
`IO` actions that are built with a `do` block are executed by executing the statements in order.

This program can be run in the same manner as the prior program:

{command helloName "hello-name" "expect -f ./run" (show := "lean --run HelloName.lean")}

If the user responds with `David`, a session of interaction with the program reads:

```commandOut helloName "expect -f ./run"
How would you like to be addressed?
David
Hello, David!
```

The type signature line is just like the one for `Hello.lean`:
```module HelloName (anchor:=sig)
def main : IO Unit := do
```
The only difference is that it ends with the keyword {moduleTerm HelloName}`do`, which initiates a sequence of commands.
Each indented line following the keyword `do` is part of the same sequence of commands.

The first two lines, which read:
```module HelloName (anchor:=setup)
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
```

retrieve the {moduleTerm HelloName (anchor := setup)}`stdin` and {moduleTerm HelloName (anchor := setup)}`stdout` handles by executing the library actions {moduleTerm HelloName (anchor := setup)}`IO.getStdin` and {moduleTerm HelloName (anchor := setup)}`IO.getStdout`, respectively.
In a {moduleTerm HelloName}`do` block, {moduleTerm HelloName}`let` has a slightly different meaning than in an ordinary expression.
Ordinarily, the local definition in a {moduleTerm HelloName}`let` can be used in just one expression, which immediately follows the local definition.
In a {moduleTerm HelloName}`do` block, local bindings introduced by {moduleTerm HelloName}`let` are available in all statements in the remainder of the {moduleTerm HelloName}`do` block, rather than just the next one.
Additionally, {moduleTerm HelloName}`let` typically connects the name being defined to its definition using `:=`, while some {moduleTerm HelloName}`let` bindings in {moduleTerm HelloName}`do` use a left arrow (`←` or `<-`) instead.
Using an arrow means that the value of the expression is an {moduleTerm HelloName}`IO` action that should be executed, with the result of the action saved in the local variable.
In other words, if the expression to the right of the arrow has type {moduleTerm HelloName}`IO α`, then the variable has type {moduleTerm HelloName}`α` in the remainder of the {moduleTerm HelloName}`do` block.
{moduleTerm HelloName (anchor := setup)}`IO.getStdin` and {moduleTerm HelloName (anchor := setup)}`IO.getStdout` are {moduleTerm HelloName (anchor := sig)}`IO` actions in order to allow {moduleTerm HelloName (anchor := setup)}`stdin` and {moduleTerm HelloName (anchor := setup)}`stdout` to be locally overridden in a program, which can be convenient.
If they were global variables as in C, then there would be no meaningful way to override them, but {moduleName HelloName}`IO` actions can return different values each time they are executed.

The next part of the {moduleTerm HelloName}`do` block is responsible for asking the user for their name:

```module HelloName (anchor:=question)
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace
```

The first line writes the question to {moduleTerm HelloName (anchor := setup)}`stdout`, the second line requests input from {moduleTerm HelloName (anchor := setup)}`stdin`, and the third line removes the trailing newline (plus any other trailing whitespace) from the input line.
The definition of {moduleTerm HelloName (anchor := question)}`name` uses `:=`, rather than `←`, because {moduleTerm HelloName}`String.dropRightWhile` is an ordinary function on strings, rather than an {moduleTerm HelloName (anchor := sig)}`IO` action.

Finally, the last line in the program is:
```module HelloName (anchor:=answer)
  stdout.putStrLn s!"Hello, {name}!"
```

It uses [string interpolation](../getting-to-know/conveniences.md#string-interpolation) to insert the provided name into a greeting string, writing the result to {moduleTerm HelloName (anchor := setup)}`stdout`.
