import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External


open FPLean


set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.HelloWorld"

#doc (Manual) "Summary" =>
%%%
tag := "hello-world-summary"
%%%

# Evaluation vs Execution
%%%
tag := none
%%%

Side effects are aspects of program execution that go beyond the evaluation of mathematical expressions, such as reading files, throwing exceptions, or triggering industrial machinery.
While most languages allow side effects to occur during evaluation, Lean does not.
Instead, Lean has a type called {moduleName}`IO` that represents _descriptions_ of programs that use side effects.
These descriptions are then executed by the language's run-time system, which invokes the Lean expression evaluator to carry out specific computations.
Values of type {moduleTerm}`IO α` are called _{moduleName}`IO` actions_.
The simplest is {moduleName}`pure`, which returns its argument and has no actual side effects.

{moduleName}`IO` actions can also be understood as functions that take the whole world as an argument and return a new world in which the side effect has occurred.
Behind the scenes, the {moduleName}`IO` library ensures that the world is never duplicated, created, or destroyed.
While this model of side effects cannot actually be implemented, as the whole universe is too big to fit in memory, the real world can be represented by a token that is passed around through the program.

An {moduleName}`IO` action {anchorName MainTypes}`main` is executed when the program starts.
{anchorName MainTypes}`main` can have one of three types:
 * {anchorTerm MainTypes}`main : IO Unit` is used for simple programs that cannot read their command-line arguments and always return exit code {anchorTerm MainTypes}`0`,
 * {anchorTerm MainTypes}`main : IO UInt32` is used for programs without arguments that may signal success or failure, and
 * {anchorTerm MainTypes}`main : List String → IO UInt32` is used for programs that take command-line arguments and signal success or failure.


# {lit}`do` Notation
%%%
tag := none
%%%

The Lean standard library provides a number of basic {moduleName}`IO` actions that represent effects such as reading from and writing to files and interacting with standard input and standard output.
These base {moduleName}`IO` actions are composed into larger {moduleName}`IO` actions using {kw}`do` notation, which is a built-in domain-specific language for writing descriptions of programs with side effects.
A {kw}`do` expression contains a sequence of _statements_, which may be:
 * expressions that represent {moduleName}`IO` actions,
 * ordinary local definitions with {kw}`let` and {lit}`:=`, where the defined name refers to the value of the provided expression, or
 * local definitions with {kw}`let` and {lit}`←`, where the defined name refers to the result of executing the value of the provided expression.

{moduleName}`IO` actions that are written with {kw}`do` are executed one statement at a time.

Furthermore, {kw}`if` and {kw}`match` expressions that occur immediately under a {kw}`do` are implicitly considered to have their own {kw}`do` in each branch.
Inside of a {kw}`do` expression, _nested actions_ are expressions with a left arrow immediately under parentheses.
The Lean compiler implicitly lifts them to the nearest enclosing {kw}`do`, which may be implicitly part of a branch of a {kw}`match` or {kw}`if` expression, and gives them a unique name.
This unique name then replaces the origin site of the nested action.


# Compiling and Running Programs
%%%
tag := none
%%%

A Lean program that consists of a single file with a {moduleName}`main` definition can be run using {lit}`lean --run FILE`.
While this can be a nice way to get started with a simple program, most programs will eventually graduate to a multiple-file project that should be compiled before running.

Lean projects are organized into _packages_, which are collections of libraries and executables together with information about dependencies and a build configuration.
Packages are described using Lake, a Lean build tool.
Use {lit}`lake new` to create a Lake package in a new directory, or {lit}`lake init` to create one in the current directory.
Lake package configuration is another domain-specific language.
Use {lit}`lake build` to build a project.

# Partiality
%%%
tag := none
%%%

One consequence of following the mathematical model of expression evaluation is that every expression must have a value.
This rules out both incomplete pattern matches that fail to cover all constructors of a datatype and programs that can fall into an infinite loop.
Lean ensures that all {kw}`match` expressions cover all cases, and that all recursive functions are either structurally recursive or have an explicit proof of termination.

However, some real programs require the possibility of looping infinitely, because they handle potentially-infinite data, such as POSIX streams.
Lean provides an escape hatch: functions whose definition is marked {kw}`partial` are not required to terminate.
This comes at a cost.
Because types are a first-class part of the Lean language, functions can return types.
Partial functions, however, are not evaluated during type checking, because an infinite loop in a function could cause the type checker to enter an infinite loop.
Furthermore, mathematical proofs are unable to inspect the definitions of partial functions, which means that programs that use them are much less amenable to formal proof.
