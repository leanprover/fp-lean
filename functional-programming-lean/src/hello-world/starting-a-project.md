# Starting a Project

As a program written in Lean becomes more serious, an ahead-of-time compiler-based workflow that results in an executable becomes more attractive.
Like other languages, Lean has tools for building multiple-file packages and managing dependencies.
The standard Lean build tool is called Lake (short for "Lean Make").
Lake is typically configured using a TOML file that declaratively specifies dependencies and describes what is to be built.
For advanced use cases, Lake can also be configured in Lean itself.

## First steps

To get started with a project that uses Lake, use the command `{{#command {first-lake} {lake} {lake new greeting} }}` in a directory that does not already contain a file or directory called `greeting`.
This creates a directory called `greeting` that contains the following files:

 * `Main.lean` is the file in which the Lean compiler will look for the `main` action.
 * `Greeting.lean` and `Greeting/Basic.lean` are the scaffolding of a support library for the program.
 * `lakefile.toml` contains the configuration that `lake` needs to build the application.
 * `lean-toolchain` contains an identifier for the specific version of Lean that is used for the project.

Additionally, `lake new` initializes the project as a Git repository and configures its `.gitignore` file to ignore intermediate build products.
Typically, the majority of the application logic will be in a collection of libraries for the program, while `Main.lean` will contain a small wrapper around these pieces that does things like parsing command lines and executing the central application logic.
To create a project in an already-existing directory, run `lake init` instead of `lake new`.

By default, the library file `Greeting/Basic.lean` contains a single definition:
```lean
{{#file_contents {lake} {first-lake/greeting/Greeting/Basic.lean} {first-lake/expected/Greeting/Basic.lean}}}
```
The library file `Greeting.lean` imports `Greeting/Basic.lean`:
```lean
{{#file_contents {lake} {first-lake/greeting/Greeting.lean} {first-lake/expected/Greeting.lean}}}
```
This means that everything defined in `Greetings/Basic.lean` is also available to files that import `Greetings.lean`.
In `import` statements, dots are interpreted as directories on disk.

The executable source `Main.lean` contains:
```lean
{{#file_contents {lake} {first-lake/greeting/Main.lean} {first-lake/expected/Main.lean}}}
```
Because `Main.lean` imports `Greetings.lean` and `Greetings.lean` imports `Greetings/Basic.lean`, the definition of `hello` is available in `main`.

To build the package, run the command `{{#command {first-lake/greeting} {lake} {lake build} }}`.
After a number of build commands scroll by, the resulting binary has been placed in `.lake/build/bin`.
Running `{{#command {first-lake/greeting} {lake} {./.lake/build/bin/greeting} }}` results in `{{#command_out {lake} {./.lake/build/bin/greeting} }}`.
Instead of running the binary directly, the command `lake exe` can be used to build the binary if necessary and then run it.
Running `{{#command {first-lake/greeting} {lake} {lake exe greeting} }}` also results in `{{#command_out {lake} {lake exe greeting} }}`.


## Lakefiles

A `lakefile.lean` describes a _package_, which is a coherent collection of Lean code for distribution, analogous to an `npm` or `nuget` package or a Rust crate.
A package may contain any number of libraries or executables.
The [documentation for Lake](https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=lake-config-toml) describes the available options in a Lake configuration.
The generated `lakefile.toml` contains the following:
```lean
{{#file_contents {lake} {first-lake/greeting/lakefile.toml} {first-lake/expected/lakefile.toml}}}
```

This initial Lake configuration consists of three items:
 * _package_ settings, at the top of the file,
 * a _library_ declaration, named `Greeting`, and
 * an _executable_, named `greeting`.

Each Lake configuration file will contain exactly one package, but any number of dependencies, libraries, or executables.
Dependencies are declarations of other Lean packages (either locally or from remote Git repositories)
The items in the Lakefile allow things like source file locations, module hierarchies, and compiler flags to be configured.
Generally speaking, however, the defaults are reasonable.
Lake configuration files written in the Lean format may additionally contain _external libraries_, which are libraries not written in Lean to be statically linked with the resulting executable, _custom targets_, which are build targets that don't fit naturally into the library/executable taxonomy, and _scripts_, which are essentially `IO` actions (similar to `main`), but that additionally have access to metadata about the package configuration.

Libraries, executables, and custom targets are all called _targets_.
By default, `lake build` builds those targets that are specified in the `defaultTargets` list.
To build a target that is not a default target, specify the target's name as an argument after `lake build`.

## Libraries and Imports

A Lean library consists of a hierarchically organized collection of source files from which names can be imported, called _modules_.
By default, a library has a single root file that matches its name.
In this case, the root file for the library `Greeting` is `Greeting.lean`.
The first line of `Main.lean`, which is `import Greeting`, makes the contents of `Greeting.lean` available in `Main.lean`.

Additional module files may be added to the library by creating a directory called `Greeting` and placing them inside.
These names can be imported by replacing the directory separator with a dot.
For instance, creating the file `Greeting/Smile.lean` with the contents:
```lean
{{#file_contents {lake} {second-lake/greeting/Greeting/Smile.lean}}}
```
means that `Main.lean` can use the definition as follows:
```lean
{{#file_contents {lake} {second-lake/greeting/Main.lean}}}
```

The module name hierarchy is decoupled from the namespace hierarchy.
In Lean, modules are units of code distribution, while namespaces are units of code organization.
That is, names defined in the module `Greeting.Smile` are not automatically in a corresponding namespace `Greeting.Smile`.
In particular, `happy` is in the `Expression` namespace.
Modules may place names into any namespace they like, and the code that imports them may `open` the namespace or not.
`import` is used to make the contents of a source file available, while `open` makes names from a namespace available in the current context without prefixes.

The line `open Expression` makes the name `Expression.happy` accessible as `happy` in `main`.
Namespaces may also be opened _selectively_, making only some of their names available without explicit prefixes.
This is done by writing the desired names in parentheses.
For example, `Nat.toFloat` converts a natural number to a `Float`.
It can be made available as `toFloat` using `open Nat (toFloat)`.
