# Running a Program

The simplest way to run a Lean program is to use the `--run` option to the Lean executable.
Create a file called `Hello.lean` and enter the following contents:
```Lean
{{#include ../../../examples/simple-hello/Hello.lean}}
```
Then, from the command line, run:
```
{{#command {simple-hello} {hello} {lean --run Hello.lean} }}
```
The program displays `{{#command_out {hello} {lean --run Hello.lean} }}` and exits.

## Anatomy of a Greeting

When Lean is invoked with the `--run` option, it invokes the program's `main` definition, which should have type `IO Unit`.
Unlike many languages, `main` is not a function, because there are no arrows (`→`) in its type.
In Lean, `main` describes an action to be taken.

As discussed in [the preceding chapter](../getting-to-know/polymorphism.md), `Unit` is the simplest inductive type.
It has a single constructor called `unit` that takes no arguments.
Languages in the C tradition have a notion of a `void` function that does not return any value at all.
In Lean, all functions take an argument and return a value, and the lack of interesting arguments or return values can be signaled by using the `Unit` type instead.
If `Bool` represents a single bit of information, `Unit represents zero bits of information.

`IO α` is the type of a program that, when executed, will either crash, fall into a loop, or return a value of type `α`.
These programs are referred to as `IO` _actions_.
Languages like Lean distinguish between _evaluation_ of expressions, which strictly adheres to the mathematical model of substitution of values for variables and reduction of sub-expressions, and _execution_ of `IO` actions, which rely on an external system to interact with the world.
`IO.println` is a function from strings to `IO` actions that, when executed, write the given string to standard output.
Because this action doesn't read any interesting information from the environment in the process of ouptutting the string, `IO.println` has type `String → IO Unit`.

## Functional Programming vs Effects

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
In order to do this, however, the cook needs peace and quite, and can't be disturbed with conversation.
The counter worker is friendly, but completely incompetent in the kitchen.
Customers interact with the counter worker, who delegates all actual cooking to the cook.

In this analogy, the cook is the Lean language.
When provided with an order, the cook faithfully and consistently delivers what is requested.
The counter worker is the surrounding run-time system that interacts with the world and can accept payments, dispense food, and have conversations with customers.
Working together, the two employees serve all the functions of the restaurant, but their responsibilities are divided, with each performing the tasks that they're best at.
Just as keeping customers away allows the cook to focus on making truly excellent coffee and sandwiches, Lean's lack of side effects allows programs to be used as part of formal mathematical proofs.
It also helps programmers understand the parts of the program in isolation from each other, because there cannot be hidden state changes that create subtle coupling between components.

## Real World Programming

The other useful way to think about side effects in Lean is by considering `IO` actions to represent functions that take the entire world as an argument, and return a value paired with a new world.
In this case, reading a line of text from standard input _is_ a pure function, because a different world is provided as an argument each time.

In reality, this model cannot be implemented.



## Input and Output

 * Ask for name and greet
 * Make analogy to café
 * Step through evaluation/execution with diagrams

