# Combining IO and Reader

One case where a reader monad can be useful is when there is some notion of the "current configuration" of the application that is passed through many recursive calls.
An example of such a program is `tree`, which recursively prints the files in the current directory and its subdirectories, indicating their tree structure using characters.
The version of `tree` in this chapter, called `doug` after the mighty Douglas Fir tree that adorns the west coast of North America, provides the option of Unicode box-drawing characters or their ASCII equivalents when indicating directory structure.

For example, the following commands create a directory structure and some empty files in a directory called `doug-demo`:
```
$ cd doug-demo
$ {{#command {doug-demo} {doug} {mkdir -p a/b/c} }}
$ {{#command {doug-demo} {doug} {mkdir -p a/d} }}
$ {{#command {doug-demo} {doug} {mkdir -p a/e/f} }}
$ {{#command {doug-demo} {doug} {touch a/b/hello} }}
$ {{#command {doug-demo} {doug} {touch a/d/another-file} }}
$ {{#command {doug-demo} {doug} {touch a/e/still-another-file-again} }}
```
Running `doug` results in the following:
```
$ {{#command {doug-demo} {doug} {doug} }}
{{#command_out {doug} {doug} }}
```

## Implementation

Internally, `doug` passes a configuration value downwards as it recursively traverses the directory structure.
This configuration contains two fields: `useASCII` determines whether to use Unicode box-drawing characters or ASCII vertical line and dash characters to indicate structure, and `currentPrefix` contains a string to prepend to each line of output.
As the current directory deepens, the prefix string accumulates indicators of being in a directory.
The configuration is a structure:
```lean
{{#example_decl Examples/MonadTransformers.lean Config}}
```
This structures has default definitions for both fields.
The default `Config` uses Unicode display with no prefix.

Users who invoke `doug` will need to be able to provide command-line arguments.
The usage information is as follows:
```lean
{{#example_decl Examples/MonadTransformers.lean usage}}
```
Accordingly, a configuration can be constructed by examining a list of command-line arguments:
```lean
{{#example_decl Examples/MonadTransformers.lean configFromArgs}}
```

The `main` function is a wrapper around an inner worker, called `dirTree`, that shows the contents of a directory using a configuration.
Before calling `dirTree`, `main` is responsible for processing command-line arguments.
It must also return the appropriate exit code to the operating system:
```lean
{{#example_decl Examples/MonadTransformers.lean OldMain}}
```

Not all paths should be shown in the directory tree.
In particular, files named `.` or `..` should be skipped, as they are actually features used for navigation rather than files _per se_.
Of those files that should be shown, there are two kinds: ordinary files and directories:
```lean
{{#example_decl Examples/MonadTransformers.lean Entry}}
```
To determine whether a file should be shown, along with which kind of entry it is, `doug` uses `toEntry`:
```lean
{{#example_decl Examples/MonadTransformers.lean toEntry}}
```
`System.FilePath.components` converts a path into a list of path components, splitting the name at directory separators.
If there is no last component, then the path is the root directory.
If the last component is a special navigation file (`.` or `..`), then the file should be excluded.
Otherwise, directories and files are wrapped in the corresponding constructors.

Lean's logic has no way to know that directory trees are finite.
Indeed, some systems allow the construction of circular directory structures.
Thus, `dirTree` is declared `partial`:
```lean
{{#example_decl Examples/MonadTransformers.lean OldDirTree}}
```
The call to `toEntry` is a [nested action](../hello-world/conveniences.md#nested-actions)—the parentheses are optional in positions where the arrow couldn't have any other meaning, such as `match`.
When the filename doesn't correspond to an entry in the tree (e.g. because it is `..`), `dirTree` does nothing.
When the filename is an ordinary file, `dirTree` calls a helper to show it with the current configuration.
When the filename is a directory, it is shown with a helper, and then its contents are recursively shown in a new configuration in which the prefix has been extended to account for being in a new directory.

Showing the names of files and directories is achieved with `showFileName` and `showDirName`:
```lean
{{#example_decl Examples/MonadTransformers.lean OldShowFile}}
```
Both of these helpers delegate to functions on `Config` that take the ASCII vs Unicode setting into account:
```lean
{{#example_decl Examples/MonadTransformers.lean filenames}}
```
Similarly, `Config.inDirectory` extends the prefix with a directory marker:
```lean
{{#example_decl Examples/MonadTransformers.lean inDirectory}}
```

Iterating an IO action over a list of directory contents is achieved using `doList`.
Because `doList` carries out all the actions in a list and does not base control-flow decisions on the values returned by any of the actions, the full power of `Monad` is not necessary, and it will work for any `Applicative`:
```lean
{{#example_decl Examples/MonadTransformers.lean doList}}
```


## Using a Custom Monad

While this implementation of `doug` works, manually passing the configuration around is verbose and error-prone.
The type system will not catch it if the wrong configuration is passed downwards, for instance.
A reader effect ensures that the same configuration is passed to all recursive calls, unless it is manually overridden, and it helps make the code less verbose.

To create a version of `IO` that is also a reader of `Config`, first define the type and its `Monad` instance, following the recipe from [the evaluator example](../monads/arithmetic.md#custom-environments):
```lean
{{#example_decl Examples/MonadTransformers.lean ConfigIO}}
```
The difference between this `Monad` instance and the one for `Reader` is that this one uses `do`-notation in the `IO` monad as the body of the function, rather than applying `next` directly to the value returned from `result`.
Any `IO` effects performed by `result` must occur before `next` is invoked, which is ensured by the `IO` monad's `bind` operator.
`ConfigIO` is not universe polymorphic because the underlying `IO` type is also not universe polymorphic.

The next step is to define a means of accessing the current configuration as part of `ConfigIO`:
```lean
{{#example_decl Examples/MonadTransformers.lean currentConfig}}
```
This is just like `read` from [the evaluator example](../monads/arithmetic.md#custom-environments), except it uses `IO`'s `pure` to return its value rather than doing so directly.
Because entering a directory modifies the current configuration for the scope of a recursive call, it will be necessary to have a way to override a configuration:
```lean
{{#example_decl Examples/MonadTransformers.lean locally}}
```

Much of the code used in `doug` has no need for configurations, and `doug` calls ordinary Lean `IO` actions from the standard library that certainly don't need a `Config`.
Ordinary `IO` actions can be run using `runIO`, which ignores the configuration argument:
```lean
{{#example_decl Examples/MonadTransformers.lean runIO}}
```

With these components, `showFileName` and `showDirName` can be updated to take their configuration arguments implicitly through the `ConfigIO` monad.
They use [nested actions](../hello-world/conveniences.md#nested-actions) to retrieve the configuration, and `runIO` to actually execute the call to `IO.println`:
```lean
{{#example_decl Examples/MonadTransformers.lean MedShowFileDir}}
```

In the new version of `dirTree`, the calls to `toEntry` and `System.FilePath.readDir` are wrapped in `runIO`.
Additionally, instead of building a new configuration and then requiring the programmer to keep track of which one to pass to recursive calls, it uses `locally` to naturally delimit the modified configuration to only a small region of the program, in which it is the _only_ valid configuration:
```lean
{{#example_decl Examples/MonadTransformers.lean MedDirTree}}
```

The new version of `main` only reverses the order of the arguments to `dirTree`:
```lean
{{#example_decl Examples/MonadTransformers.lean MedMain}}
```

This custom monad has a number of advantages over passing configurations manually:

 1. It is easier to ensure that configurations are passed down unchanged, except when changes are desired
 2. The concern of passing the configuration onwards is more clearly separated from the concern of printing directory contents
 3. As the program grows, there will be more and more intermediate layers that do nothing with configurations except propagate them, and these layers don't need to be rewritten as the configuration logic changes

However, there are also some clear downsides:

 1. As the program evolves and the monad requires more features, each of the basic operators such as `locally` and `currentConfig` will need to be updated
 2. Wrapping ordinary `IO` actions in `runIO` is noisy and distracts from the flow of the program
 3. Writing monads by hand is repetitive, and the technique for adding a reader effect to another monad is a design pattern that requires documentation and communication

Using a technique called _monad transformers_, all of these downsides can be addressed.
A monad transformer takes a monad as an argument and returns a new monad.
Monad transformers consist of:
 1. A definition of the transformer itself, which is typically a function from types to types
 2. A `Monad` instance that assumes the inner type is already a monad
 3. An operator to "lift" an action from the inner monad to the transformed monad, akin to `runIO`

## Adding a Reader to Any Monad

Adding a reader effect to `IO` was accomplished in `ConfigIO` by wrapping `IO α` in a function type.
The Lean standard library contains a function that can do this to _any_ polymorphic type, called `ReaderT`:
```lean
{{#example_decl Examples/MonadTransformers.lean MyReaderT}}
```
Its arguments are as follows:
 * `ρ` is the environment that is accessible to the reader
 * `m` is the monad that is being transformed, such as `IO`
 * `α` is the type of values being returned by the monadic computation
Both `α` and `ρ` are in the same universe because the operator that retrieves the environment in the monad will have type `m ρ`.

With `ReaderT`, `ConfigIO` becomes:
```lean
{{#example_decl Examples/MonadTransformers.lean ReaderTConfigIO}}
```
It is an `abbrev` because `ReaderT` has many useful features defined in the standard library that a non-reducible definition would hide.
Rather than taking responsibility for making these work directly for `ConfigIO`, it's easier to simply have `ConfigIO` behave identically to `ReaderT Config IO`.

The manually-written `currentConfig` obtained the environment out of the reader.
This effect is available in a generic form for all uses of `ReaderT`, under the name `read`:
```lean
{{#example_decl Examples/MonadTransformers.lean MyReaderTread}}
```

The `Monad` instance for `ReaderT` is essentially the same as the `Monad` instance for `ConfigIO`, except `IO` has been replaced by some arbitrary monad argument `m`:
```lean
{{#example_decl Examples/MonadTransformers.lean MonadMyReaderT}}
```
Definitions such as `ReaderT` that build an extended monad out of some underlying monad are called _monad transformers_.

The next step is to eliminate uses of `runIO`.
When Lean encounters a mismatch in monad types, it automatically attempts to use a type class called `MonadLift` to transform the actual monad into the expected monad.
This process is similar to the use of coercions.
`MonadLift` is defined as follows:
```lean
{{#example_decl Examples/MonadTransformers.lean MyMonadLift}}
```
The method `monadLift` translates from one monad to another.
The process is called "lifting" because it takes an action in the embedded monad and makes it into an action in the surrounding monad.
In this case, it will be used to "lift" from `IO` to `ReaderT Config IO`, though the instance works for _any_ inner monad `m`:
```lean
{{#example_decl Examples/MonadTransformers.lean MonadLiftReaderT}}
```
The implementation of `monadLift` is very similar to that of `runIO`.
Indeed, it is enough to define `showFileName` and `showDirName` without using `runIO`:
```lean
{{#example_decl Examples/MonadTransformers.lean showFileAndDir}}
```

One final operation from the original `ConfigIO` remains to be translated to a use of `ReaderT`: `locally`.
The definition can be translated directly to `ReaderT`, but the Lean standard library provides a more general version.
The standard version is called `withReader`, and it is part of a type class called `MonadWithReader`:
```lean
{{#example_decl Examples/MonadTransformers.lean MyMonadWithReader}}
```
The environment `ρ` is an `outParam` to allow Lean to find the instance even when the type of the function being used to modify the environment is not yet known.
The `withReader` operation is exported, so that it doesn't need to be written with the type class name before it:
```lean
{{#example_decl Examples/MonadTransformers.lean exportWithReader}}
```
The instance for `ReaderT` is essentially the same as the definition of `locally`:
```lean
{{#example_decl Examples/MonadTransformers.lean ReaderTWithReader}}
```

The `WithReader` type class exists because `monadLift` is not capable of lifting `withReader`.
This is because `monadLift` expects to work on a single monadic action, but `withReader` _changes_ a monadic action.
`IO` actions can automatically be lifted to `ReaderT ρ IO` actions, but lifting `withReader` requires the ability to go _backwards_, because the underlying action being transformed will also have more layers. TODO this sentence is really unclear - figure out how to discuss "negative occurrence"
The type classes are set up such that `withReader` will be lifted as much as possible. TODO vague - fix me

With these definitions in place, the new version of `dirTree` can be written:
```lean
{{#example_decl Examples/MonadTransformers.lean readerTDirTree}}
```
Aside from replacing `locally` with `withReader`, it is the same as before.


Replacing the custom `ConfigIO` type with `ReaderT` did not save a large number of lines of code in this section.
However, rewriting the code using components from the standard library does have long-term benefits.
First, readers who know about `ReaderT` don't need to take time to understand the `Monad` instance for `ConfigIO`, working backwards to the meaning of monad itself.
Instead, they can be confident in their initial understanding.
Next, adding further effects to the monad (such as a state effect to count the files in each directory and display a count at the end) requires far fewer changes to the code, because the monad transformers and `MonadLift` instances provided in the library work well together.
Finally, using a set of type classes included in the standard library, polymorphic code can be written in such a way that it can work with a variety of monads without having to care about details like the order in which the monad transformers were applied.
Just as some functions work in any monad, others can work in any monad that provides a certain type of state, or a certain type of exceptions, without having to specifically describe the _way_ in which a particular concrete monad provides the state or exceptions.

## Exercises

### Controlling the Display of Dotfiles

Files whose names being with a dot character (`'.'`) typically represent files that should usually be hidden, such as source-control metadata and configuration files.
Modify `doug` with an option to show or hide filenames that begin with a dot.
This option should be controlled with a `-a` command-line option.

### Starting Directory as Argument

Modify `doug` so that it takes a starting directory as an additional command-line argument.

