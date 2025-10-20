import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples/second-lake/greeting"
set_option verso.exampleModule "Main"

#doc (Manual) "Starting a Project" =>
%%%
tag := "starting-a-project"
%%%

As a program written in Lean becomes more serious, an ahead-of-time compiler-based workflow that results in an executable becomes more attractive.
Like other languages, Lean has tools for building multiple-file packages and managing dependencies.
The standard Lean build tool is called Lake (short for “Lean Make”).
Lake is typically configured using a TOML file that declaratively specifies dependencies and describes what is to be built.
For advanced use cases, Lake can also be configured in Lean itself.

# First steps
%%%
tag := "lake-new"
%%%


To get started with a project that uses Lake, use the command {command lake "first-lake"}`lake new greeting` in a directory that does not already contain a file or directory called {lit}`greeting`.
This creates a directory called {lit}`greeting` that contains the following files:

 * {lit}`Main.lean` is the file in which the Lean compiler will look for the {lit}`main` action.
 * {lit}`Greeting.lean` and {lit}`Greeting/Basic.lean` are the scaffolding of a support library for the program.
 * {lit}`lakefile.toml` contains the configuration that {lit}`lake` needs to build the application.
 * {lit}`lean-toolchain` contains an identifier for the specific version of Lean that is used for the project.

Additionally, {lit}`lake new` initializes the project as a Git repository and configures its {lit}`.gitignore` file to ignore intermediate build products.
Typically, the majority of the application logic will be in a collection of libraries for the program, while {lit}`Main.lean` will contain a small wrapper around these pieces that does things like parsing command lines and executing the central application logic.
To create a project in an already-existing directory, run {lit}`lake init` instead of {lit}`lake new`.

By default, the library file {lit}`Greeting/Basic.lean` contains a single definition:
```file lake "first-lake/greeting/Greeting/Basic.lean" "Greeting/Basic.lean"
def hello := "world"
```

The library file {lit}`Greeting.lean` imports {lit}`Greeting/Basic.lean`:
```file lake "first-lake/greeting/Greeting.lean" "Greeting.lean"
-- This module serves as the root of the `Greeting` library.
-- Import modules here that should be built as part of the library.
import Greeting.Basic
```

This means that everything defined in {lit}`Greeting/Basic.lean` is also available to files that import {lit}`Greeting.lean`.
In {kw}`import` statements, dots are interpreted as directories on disk.

The executable source {lit}`Main.lean` contains:
```file lake "first-lake/greeting/Main.lean" "Main.lean"
import Greeting

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

Because {lit}`Main.lean` imports {lit}`Greeting.lean` and {lit}`Greeting.lean` imports {lit}`Greeting/Basic.lean`, the definition of {lit}`hello` is available in {lit}`main`.

To build the package, run the command {command lake "first-lake/greeting"}`lake build`.
After a number of build commands scroll by, the resulting binary has been placed in {lit}`.lake/build/bin`.
Running {command lake "first-lake/greeting"}`./.lake/build/bin/greeting` results in {commandOut lake}`./.lake/build/bin/greeting`.
Instead of running the binary directly, the command {lit}`lake exe` can be used to build the binary if necessary and then run it.
Running {command lake "first-lake/greeting"}`lake exe greeting` also results in {commandOut lake}`lake exe greeting`.


# Lakefiles
%%%
tag := "lakefiles"
%%%

A {lit}`lakefile.toml` describes a _package_, which is a coherent collection of Lean code for distribution, analogous to an {lit}`npm` or {lit}`nuget` package or a Rust crate.
A package may contain any number of libraries or executables.
The [documentation for Lake](https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=lake-config-toml) describes the available options in a Lake configuration.
The generated {lit}`lakefile.toml` contains the following:
```file lake "first-lake/greeting/lakefile.toml" "lakefile.toml"
name = "greeting"
version = "0.1.0"
defaultTargets = ["greeting"]

[[lean_lib]]
name = "Greeting"

[[lean_exe]]
name = "greeting"
root = "Main"
```


This initial Lake configuration consists of three items:
 * _package_ settings, at the top of the file,
 * a _library_ declaration, named {lit}`Greeting`, and
 * an _executable_, named {lit}`greeting`.

Each Lake configuration file will contain exactly one package, but any number of dependencies, libraries, or executables.
By convention, package and executable names begin with a lowercase letter, while libraries begin with an uppercase letter.
Dependencies are declarations of other Lean packages (either locally or from remote Git repositories)
The items in the Lake configuration file allow things like source file locations, module hierarchies, and compiler flags to be configured.
Generally speaking, however, the defaults are reasonable.
Lake configuration files written in the Lean format may additionally contain _external libraries_, which are libraries not written in Lean to be statically linked with the resulting executable, _custom targets_, which are build targets that don't fit naturally into the library/executable taxonomy, and _scripts_, which are essentially {moduleName}`IO` actions (similar to {moduleName}`main`), but that additionally have access to metadata about the package configuration.

Libraries, executables, and custom targets are all called _targets_.
By default, {lit}`lake build` builds those targets that are specified in the {lit}`defaultTargets` list.
To build a target that is not a default target, specify the target's name as an argument after {lit}`lake build`.

# Libraries and Imports
%%%
tag := "libraries-and-imports"
%%%

A Lean library consists of a hierarchically organized collection of source files from which names can be imported, called _modules_.
By default, a library has a single root file that matches its name.
In this case, the root file for the library {lit}`Greeting` is {lit}`Greeting.lean`.
The first line of {lit}`Main.lean`, which is {moduleTerm}`import Greeting`, makes the contents of {lit}`Greeting.lean` available in {lit}`Main.lean`.

Additional module files may be added to the library by creating a directory called {lit}`Greeting` and placing them inside.
These names can be imported by replacing the directory separator with a dot.
For instance, creating the file {lit}`Greeting/Smile.lean` with the contents:
```file lake "second-lake/greeting/Greeting/Smile.lean" "Greeting/Smile.lean"
def Expression.happy : String := "a big smile"
```

means that {lit}`Main.lean` can use the definition as follows:
```file lake "second-lake/greeting/Main.lean" "Main.lean"
import Greeting
import Greeting.Smile

open Expression

def main : IO Unit :=
  IO.println s!"Hello, {hello}, with {happy}!"
```


The module name hierarchy is decoupled from the namespace hierarchy.
In Lean, modules are units of code distribution, while namespaces are units of code organization.
That is, names defined in the module {lit}`Greeting.Smile` are not automatically in a corresponding namespace {lit}`Greeting.Smile`.
In particular, {moduleName (module:=Greeting.Smile) (show:=happy)}`Expression.happy` is in the {lit}`Expression` namespace.
Modules may place names into any namespace they like, and the code that imports them may {kw}`open` the namespace or not.
{kw}`import` is used to make the contents of a source file available, while {kw}`open` makes names from a namespace available in the current context without prefixes.

The line {moduleTerm}`open Expression` makes the name {moduleName (module:=Greeting.Smile)}`Expression.happy` accessible as {moduleName}`happy` in {moduleName}`main`.
Namespaces may also be opened _selectively_, making only some of their names available without explicit prefixes.
This is done by writing the desired names in parentheses.
For example, {moduleTerm (module:=Aux)}`Nat.toFloat` converts a natural number to a {moduleTerm (module:=Aux)}`Float`.
It can be made available as {moduleName (module:=Aux)}`toFloat` using {moduleTerm (module:=Aux)}`open Nat (toFloat)`.
