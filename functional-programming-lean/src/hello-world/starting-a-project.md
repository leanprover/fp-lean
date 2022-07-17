# Starting a Project

As a program written in Lean becomes more serious, an ahead-of-time compiler-based workflow that results in an executable becomes more attractive.
The standard Lean build tool is called Lake (short for "Lean Make"), and it is configured in Lean.
Just as Lean contains a special-purpose language for writing programs with effects (the `do` language), Lake contains a special-purpose for configuring builds.
These languages are referred to as _embedded domain-specific languages_ (or sometimes _domain-specific embedded languages_, abbreviated EDSL or DSEL).
They are _domain-specific_ in the sense that they are used for a particular purpose, with concepts from some sub-domain, and they are typically not suitable for general-purpose programming.
The are _embedded_ because they occur inside another language's syntax.
While Lean contains rich facilities for creating EDSLs, they are beyond the scope of this book.

## First steps

To get started with a project that uses Lake, the command `{{#command {first-lake} {lake} {lake new greeting} }}` in a directory that does not already contain a file or directory called `greeting`.
This creates a directory called `greeting` that contains the following files:

 * `Main.lean` is the file in which the Lean compiler will look for the `main` action.
 * `Greeting.lean` is the scaffolding of a support library for the program.
 * `lakefile.lean` contains the configuration that `lake` needs to build the application.
 * `lean-toolchain` contains an identifier for the specific version of Lean that is used for the project.

Additionally, `lake new` initializes the project as a Git repository and configures its `.gitignore` file to ignore intermediate build products.
Typically, the majority of the application logic will be in a collection of libraries for the program, while `Main.lean` will contain a small wrapper around these pieces that does things like parsing command lines and executing the central application logic.
To create a project in an already-existing directory, run `lake init` instead of `lake new`.

By default, the library file `Greeting.lean` contains a single definition:
```Lean
{{#file_contents {lake} {first-lake/greeting/Greeting.lean} {first-lake/expected/Greeting.lean}}}
```
while the executable source `Main.lean` contains:
```Lean
{{#file_contents {lake} {first-lake/greeting/Main.lean} {first-lake/expected/Main.lean}}}
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

This initial Lakefile consists of three items:
 * a _package_ declaration, named `greeting`,
 * a _library_ declaration, named `Greeting`, and
 * an _executable_, also named `greeting`.
 
Each Lakefile will contain exactly one package, but any number of libraries or executables.
Additionally, Lakefiles may contain _external libraries_, which are libraries not written in Lean to be statically linked with the resulting executable, _custom targets_, which are build targets that don't fit naturally into the library/executable taxonomy, _dependencies_, which are declarations of other Lean packages (either locally or from remote Git repositories), and _scripts_, which are essentially `IO` actions (similar to `main`), but that additionally have access to metadata about the package configuration.
The items in the Lakefile allow things like source file locations, module hierarchies, and compiler flags to be configured.
Generally speaking, however, the defaults are reasonable.

Libraries, executables, and custom targets are all called _targets_.
By default, `lake build` builds those targets that are annotated with `@[defaultTarget]`.
This annotation is an _attribute_, which is metadata that can be associated with a Lean declaration.
Attributes are similar to Java annotations or C# and Rust attributes.
They are used pervasively throughout Lean.
To build a target that is not annotated with `@[defaultTarget]`, specify the target's name as an argument after `lake build`.

## Libraries and Imports

A Lean library consists of a hierarchically organized collection of source files from which names can be imported, called _modules_.
By default, a library has a single root file that matches its name.
In this case, the root file for the library `Greeting` is `Greeting.lean`.
The first line of `Main.lean`, which is `import Greeting`, makes the contents of `Greeting.lean` available in `Main.lean`.

Further module files may be added to the library by creating a directory called `Greeting` and placing them inside.
These names can be imported by replacing the directory separator with a dot.
For instance, creating the file `Greeting/Smile.lean` with the contents:
```Lean
{{#file_contents {lake} {second-lake/greeting/Greeting/Smile.lean}}}
```
means that `Main.lean` can use the definition as follows:
```Lean
{{#file_contents {lake} {second-lake/greeting/Main.lean}}}
```

The module name hierarchy is separate from the namespace hierarchy.
That is, names defined in the module `Greeting.Smile` are not in a corresponding namespace `Greeting.Smile`.
Modules may place names into any namespace they like, and the code that imports them may `open` the namespace or not.
`import` is used to make the contents of a source file available, while `open` makes names from a namespace available in the current context.
In the Lakefile, the line `import Lake` makes the contents of the `Lake` module available, while the like `open Lake DSL` makes the contents of the `Lake` and `DSL` namespaces available without any prefixes.


