# Starting a Project

As a program written in Lean becomes more serious, an ahead-of-time compiler-based workflow that results in an executable becomes more attractive.
The standard Lean build tool is called Lake (short for "Lean Make"), and it is configured in Lean.
Just as Lean contains a special-purpose language for writing programs with effects (the `do` language), Lake contains a special-purpose for configuring builds.
These languages are referred to as _embedded domain-specific languages_ (or sometimes _domain-specific embedded languages_, abbreviated EDSL or DSEL).
The are _domain-specific_ in the sense that they are used for a particular purpose, with concepts from some sub-domain, and they are typically not suitable for general-purpose programming.
The are _embedded_ because they occur inside another language's syntax.
While Lean contains rich facilities for creating EDSLs, they are beyond the scope of this book.

## First steps

To get started with a project that uses Lake, the command `{{#command {first-lake} {lake} {lake new greeting} }}` in a directory that does not already contain a file or directory called `greeting`.
This creates a directory called `greeting` that contains the following files:

 * `Main.lean` is the file in which the Lean compiler will look for the `main` action.
 * `Greeting.lean` is the scaffolding of a support library for the program.
 * `lakefile.lean` contains the configuration that `lake` needs to build the application.
 * `lean-toolchain` contains an identifier for the specific version of Lean that is used for the project.

Additionally, `lake new` initializes the project as a Git repository and configures it to ignore intermediate build products.
Typically, the majority of the application logic will be in a collection of libraries for the program, while `Main.lean` will contain a small wrapper around these pieces that does things like parsing command lines and executing the central application logic.

By default, the library file `Greeting.lean` contains a single definition:
```Lean
-- TODO externalize and test
def hello := "world"
```
while the executable source `Main.lean` contains:
```Lean
-- TODO externalize and test
import Greeting

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```
The `import` line makes the contents of `Greeting.lean` available in `Main.lean`.

To build the package, run the command `{{#command {first-lake/greeting} {lake} {lake build} }}`.
After a number of build commands scroll by, the resulting binary has been placed in `build/bin`.
Running `{{#command {first-lake/greeting} {lake} {./build/bin/greeting} }}` results in `{{#command_out {lake} {./build/bin/greeting} }}`.

## Lakefiles

A `lakefile.lean` describes a _package_, which is a coherent collection of Lean code for distribution, analogous to an `npm` or `nuget` package or a Rust crate.
A package may contain any number of libraries or executables.
While the [documentation for Lake](https://github.com/leanprover/lake#readme) describes the available options in a lakefile, it makes use of a number of Lean features that have not yet been described here.
The generated `lakefile.lean` contains the following:
```
{{#file_contents {lake} {first-lake/greeting/lakefile.lean} {first-lake/expected/lakefile.lean}}}
```

The initial Lakefile consists of three items:


## Imports


