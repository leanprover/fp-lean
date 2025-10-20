import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "DirTree"

#doc (Manual) "Combining IO and Reader" =>
%%%
tag := "io-reader"
%%%

One case where a reader monad can be useful is when there is some notion of the “current configuration” of the application that is passed through many recursive calls.
An example of such a program is {lit}`tree`, which recursively prints the files in the current directory and its subdirectories, indicating their tree structure using characters.
The version of {lit}`tree` in this chapter, called {lit}`doug` after the mighty Douglas Fir tree that adorns the west coast of North America, provides the option of Unicode box-drawing characters or their ASCII equivalents when indicating directory structure.


For example, the following commands create a directory structure and some empty files in a directory called {lit}`doug-demo`:
```commands doug "doug-demo"
$$ cd doug-demo
$ mkdir -p a/b/c
$ mkdir -p a/d
$ mkdir -p a/e/f
$ touch a/b/hello
$ touch a/d/another-file
$ touch a/e/still-another-file-again
```
Running {lit}`doug` results in the following:
```commands doug "doug-demo"
$ doug
├── doug-demo/
│   ├── a/
│   │   ├── b/
│   │   │   ├── c/
│   │   │   ├── hello
│   │   ├── d/
│   │   │   ├── another-file
│   │   ├── e/
│   │   │   ├── f/
│   │   │   ├── still-another-file-again
```

# Implementation
%%%
tag := "reader-io-implementation"
%%%

Internally, {lit}`doug` passes a configuration value downwards as it recursively traverses the directory structure.
This configuration contains two fields: {anchorName Config}`useASCII` determines whether to use Unicode box-drawing characters or ASCII vertical line and dash characters to indicate structure, and {anchorName Config}`currentPrefix` contains a string to prepend to each line of output.
As the current directory deepens, the prefix string accumulates indicators of being in a directory.
The configuration is a structure:

```anchor Config
structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""
```
This structure has default definitions for both fields.
The default {anchorName Config}`Config` uses Unicode display with no prefix.

:::paragraph
Users who invoke {lit}`doug` will need to be able to provide command-line arguments.
The usage information is as follows:

```anchor usage
def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"
```
Accordingly, a configuration can be constructed by examining a list of command-line arguments:

```anchor configFromArgs
def configFromArgs : List String → Option Config
  | [] => some {} -- both fields default
  | ["--ascii"] => some {useASCII := true}
  | _ => none
```
:::

The {anchorName OldMain}`main` function is a wrapper around an inner worker, called {anchorName OldMain}`dirTree`, that shows the contents of a directory using a configuration.
Before calling {anchorName OldMain}`dirTree`, {anchorName OldMain}`main` is responsible for processing command-line arguments.
It must also return the appropriate exit code to the operating system:

```anchor OldMain
def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | some config =>
    dirTree config (← IO.currentDir)
    pure 0
  | none =>
    IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
    IO.eprintln usage
    pure 1
```
{anchorName OldMain}`IO.eprintln` is a version of {anchorName OldShowFile}`IO.println` that outputs to standard error.

Not all paths should be shown in the directory tree.
In particular, files named {lit}`.` or {lit}`..` should be skipped, as they are actually features used for navigation rather than files _per se_.
Of those files that should be shown, there are two kinds: ordinary files and directories:

```anchor Entry
inductive Entry where
  | file : String → Entry
  | dir : String → Entry
```
To determine whether a file should be shown, along with which kind of entry it is, {lit}`doug` uses {anchorName toEntry}`toEntry`:

```anchor toEntry
def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
    pure (some (if (← path.isDir) then .dir name else .file name))
```
{anchorName names}`System.FilePath.components` converts a path into a list of path components, splitting the name at directory separators.
If there is no last component, then the path is the root directory.
If the last component is a special navigation file ({lit}`.` or {lit}`..`), then the file should be excluded.
Otherwise, directories and files are wrapped in the corresponding constructors.

Lean's logic has no way to know that directory trees are finite.
Indeed, some systems allow the construction of circular directory structures.
Thus, {anchorName OldDirTree}`dirTree` is declared {kw}`partial`:

```anchor OldDirTree
partial def dirTree (cfg : Config) (path : System.FilePath) : IO Unit := do
  match ← toEntry path with
  | none => pure ()
  | some (.file name) => showFileName cfg name
  | some (.dir name) =>
    showDirName cfg name
    let contents ← path.readDir
    let newConfig := cfg.inDirectory
    doList (contents.qsort dirLT).toList fun d =>
      dirTree newConfig d.path
```
The call to {anchorName OldDirTree}`toEntry` is a {ref "nested-actions"}[nested action]—the parentheses are optional in positions where the arrow couldn't have any other meaning, such as {kw}`match`.
When the filename doesn't correspond to an entry in the tree (e.g. because it is {lit}`..`), {anchorName OldDirTree}`dirTree` does nothing.
When the filename points to an ordinary file, {anchorName OldDirTree}`dirTree` calls a helper to show it with the current configuration.
When the filename points to a directory, it is shown with a helper, and then its contents are recursively shown in a new configuration in which the prefix has been extended to account for being in a new directory.
The contents of the directory are sorted in order to make the output deterministic, compared according to {anchorName compareEntries'}`dirLT`.
```anchor compareEntries'
def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName
```

Showing the names of files and directories is achieved with {anchorName OldShowFile}`showFileName` and {anchorName OldShowFile}`showDirName`:

```anchor OldShowFile
def showFileName (cfg : Config) (file : String) : IO Unit := do
  IO.println (cfg.fileName file)

def showDirName (cfg : Config) (dir : String) : IO Unit := do
  IO.println (cfg.dirName dir)
```
Both of these helpers delegate to functions on {anchorName filenames}`Config` that take the ASCII vs Unicode setting into account:

```anchor filenames
def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"
```
Similarly, {anchorName inDirectory}`Config.inDirectory` extends the prefix with a directory marker:

```anchor inDirectory
def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}
```

Iterating an IO action over a list of directory contents is achieved using {anchorName doList}`doList`.
Because {anchorName doList}`doList` carries out all the actions in a list and does not base control-flow decisions on the values returned by any of the actions, the full power of {anchorName ConfigIO}`Monad` is not necessary, and it will work for any {anchorName doList}`Applicative`:

```anchor doList
def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *>
    doList xs action
```


# Using a Custom Monad
%%%
tag := "reader-io-custom-monad"
%%%

While this implementation of {lit}`doug` works, manually passing the configuration around is verbose and error-prone.
The type system will not catch it if the wrong configuration is passed downwards, for instance.
A reader effect ensures that the same configuration is passed to all recursive calls, unless it is manually overridden, and it helps make the code less verbose.

To create a version of {anchorName ConfigIO}`IO` that is also a reader of {anchorName ConfigIO}`Config`, first define the type and its {anchorName ConfigIO}`Monad` instance, following the recipe from {ref "custom-environments"}[the evaluator example]:

```anchor ConfigIO
def ConfigIO (α : Type) : Type :=
  Config → IO α

instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind result next := fun cfg => do
    let v ← result cfg
    next v cfg
```
The difference between this {anchorName ConfigIO}`Monad` instance and the one for {anchorName Reader (module := Examples.Monads.Class)}`Reader` is that this one uses {kw}`do`-notation in the {anchorName ConfigIO}`IO` monad as the body of the function that {anchorName ConfigIO}`bind` returns, rather than applying {anchorName ConfigIO}`next` directly to the value returned from {anchorName ConfigIO}`result`.
Any {anchorName ConfigIO}`IO` effects performed by {anchorName ConfigIO}`result` must occur before {anchorName ConfigIO}`next` is invoked, which is ensured by the {anchorName ConfigIO}`IO` monad's {anchorName ConfigIO}`bind` operator.
{anchorName ConfigIO}`ConfigIO` is not universe polymorphic because the underlying {anchorName ConfigIO}`IO` type is also not universe polymorphic.

Running a {anchorName ConfigIO}`ConfigIO` action involves transforming it into an {anchorName ConfigIO}`IO` action by providing it with a configuration:

```anchor ConfigIORun
def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg
```
This function is not really necessary, as a caller could simply provide the configuration directly.
However, naming the operation can make it easier to see which parts of the code are intended to run in which monad.

The next step is to define a means of accessing the current configuration as part of {anchorName ConfigIO}`ConfigIO`:

```anchor currentConfig
def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg
```
This is just like {anchorName Reader (module := Examples.Monads.Class)}`read` from {ref "custom-environments"}[the evaluator example], except it uses {anchorName ConfigIO}`IO`'s {anchorName ConfigIO}`pure` to return its value rather than doing so directly.
Because entering a directory modifies the current configuration for the scope of a recursive call, it will be necessary to have a way to override a configuration:

```anchor locally
def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action (change cfg)
```

Much of the code used in {lit}`doug` has no need for configurations, and {lit}`doug` calls ordinary Lean {anchorName ConfigIO}`IO` actions from the standard library that certainly don't need a {anchorName ConfigIO}`Config`.
Ordinary {anchorName ConfigIO}`IO` actions can be run using {anchorName runIO}`runIO`, which ignores the configuration argument:

```anchor runIO
def runIO (action : IO α) : ConfigIO α :=
  fun _ => action
```

With these components, {anchorName MedShowFileDir}`showFileName` and {anchorName MedShowFileDir}`showDirName` can be updated to take their configuration arguments implicitly through the {anchorName ConfigIO}`ConfigIO` monad.
They use {ref "nested-actions"}[nested actions] to retrieve the configuration, and {anchorName runIO}`runIO` to actually execute the call to {anchorName MedShowFileDir}`IO.println`:

```anchor MedShowFileDir
def showFileName (file : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).fileName file))

def showDirName (dir : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).dirName dir))
```

In the new version of {anchorName MedDirTree}`dirTree`, the calls to {anchorName MedDirTree}`toEntry` and {anchorName MedDirTree}`readDir` are wrapped in {anchorName runIO}`runIO`.
Additionally, instead of building a new configuration and then requiring the programmer to keep track of which one to pass to recursive calls, it uses {anchorName MedDirTree}`locally` to naturally delimit the modified configuration to only a small region of the program, in which it is the _only_ valid configuration:

```anchor MedDirTree
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← runIO (toEntry path) with
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← runIO path.readDir
      locally (·.inDirectory)
        (doList (contents.qsort dirLT).toList fun d =>
          dirTree d.path)
```

The new version of {anchorName MedMain}`main` uses {anchorName ConfigIORun}`ConfigIO.run` to invoke {anchorName MedMain}`dirTree` with the initial configuration:

```anchor MedMain
def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config =>
      (dirTree (← IO.currentDir)).run config
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
      IO.eprintln usage
      pure 1
```

This custom monad has a number of advantages over passing configurations manually:

 1. It is easier to ensure that configurations are passed down unchanged, except when changes are desired
 2. The concern of passing the configuration onwards is more clearly separated from the concern of printing directory contents
 3. As the program grows, there will be more and more intermediate layers that do nothing with configurations except propagate them, and these layers don't need to be rewritten as the configuration logic changes

However, there are also some clear downsides:

 1. As the program evolves and the monad requires more features, each of the basic operators such as {anchorName locally}`locally` and {anchorName currentConfig}`currentConfig` will need to be updated
 2. Wrapping ordinary {anchorName ConfigIO}`IO` actions in {anchorName runIO}`runIO` is noisy and distracts from the flow of the program
 3. Writing monads instances by hand is repetitive, and the technique for adding a reader effect to another monad is a design pattern that requires documentation and communication overhead

Using a technique called _monad transformers_, all of these downsides can be addressed.
A monad transformer takes a monad as an argument and returns a new monad.
Monad transformers consist of:
 1. A definition of the transformer itself, which is typically a function from types to types
 2. A {anchorName ConfigIO}`Monad` instance that assumes the inner type is already a monad
 3. An operator to “lift” an action from the inner monad to the transformed monad, akin to {anchorName runIO}`runIO`

# Adding a Reader to Any Monad
%%%
tag := "ReaderT"
%%%

Adding a reader effect to {anchorName ConfigIO}`IO` was accomplished in {anchorName ConfigIO}`ConfigIO` by wrapping {anchorTerm ConfigIO}`IO α` in a function type.
The Lean standard library contains a function that can do this to _any_ polymorphic type, called {anchorName MyReaderT}`ReaderT`:

```anchor MyReaderT
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) :
    Type (max u v) :=
  ρ → m α
```
Its arguments are as follows:
 * {anchorName MyReaderT}`ρ` is the environment that is accessible to the reader
 * {anchorName MyReaderT}`m` is the monad that is being transformed, such as {anchorName ConfigIO}`IO`
 * {anchorName MyReaderT}`α` is the type of values being returned by the monadic computation
Both {anchorName MyReaderT}`α` and {anchorName MyReaderT}`ρ` are in the same universe because the operator that retrieves the environment in the monad will have type {anchorTerm MyReaderTread}`m ρ`.

:::paragraph
With {anchorName MyReaderT}`ReaderT`, {anchorName ConfigIO}`ConfigIO` becomes:

```anchor ReaderTConfigIO
abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α
```
It is an {kw}`abbrev` because {anchorName ReaderTConfigIO}`ReaderT` has many useful features defined in the standard library that a non-reducible definition would hide.
Rather than taking responsibility for making these work directly for {anchorName ConfigIO}`ConfigIO`, it's easier to simply have {anchorName ReaderTConfigIO}`ConfigIO` behave identically to {anchorTerm ReaderTConfigIO}`ReaderT Config IO`.
:::

:::paragraph
The manually-written {anchorName currentConfig}`currentConfig` obtained the environment out of the reader.
This effect can be defined in a generic form for all uses of {anchorName MyReaderTread}`ReaderT`, under the name {anchorName MonadReader}`read`:

```anchor MyReaderTread
def read [Monad m] : ReaderT ρ m ρ :=
   fun env => pure env
```
However, not every monad that provides a reader effect is built with {anchorName MyReaderT}`ReaderT`.
The type class {anchorName MonadReader}`MonadReader` allows any monad to provide a {anchorName MonadReader}`read` operator:

```anchor MonadReader
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) :
    Type (max (u + 1) v) where
  read : m ρ

instance [Monad m] : MonadReader ρ (ReaderT ρ m) where
  read := fun env => pure env

export MonadReader (read)
```
The type {anchorName MonadReader}`ρ` is an output parameter because any given monad typically only provides a single type of environment through a reader, so automatically selecting it when the monad is known makes programs more convenient to write.
:::

The {anchorName ConfigIO}`Monad` instance for {anchorName MyReaderT}`ReaderT` is essentially the same as the {anchorName ConfigIO}`Monad` instance for {anchorName ConfigIO}`ConfigIO`, except {anchorName ConfigIO}`IO` has been replaced by some arbitrary monad argument {anchorName MonadMyReaderT}`m`:

```anchor MonadMyReaderT
instance [Monad m] : Monad (ReaderT ρ m) where
  pure x := fun _ => pure x
  bind result next := fun env => do
    let v ← result env
    next v env
```


The next step is to eliminate uses of {anchorName runIO}`runIO`.
When Lean encounters a mismatch in monad types, it automatically attempts to use a type class called {anchorName MyMonadLift}`MonadLift` to transform the actual monad into the expected monad.
This process is similar to the use of coercions.
{anchorName MyMonadLift}`MonadLift` is defined as follows:

```anchor MyMonadLift
class MonadLift (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α
```
The method {anchorName MyMonadLift}`monadLift` translates from the monad {anchorName MyMonadLift}`m` to the monad {anchorName MyMonadLift}`n`.
The process is called “lifting” because it takes an action in the embedded monad and makes it into an action in the surrounding monad.
In this case, it will be used to “lift” from {anchorName ConfigIO}`IO` to {anchorTerm ReaderTConfigIO}`ReaderT Config IO`, though the instance works for _any_ inner monad {anchorName MonadLiftReaderT}`m`:

```anchor MonadLiftReaderT
instance : MonadLift m (ReaderT ρ m) where
  monadLift action := fun _ => action
```
The implementation of {anchorName MonadLiftReaderT}`monadLift` is very similar to that of {anchorName runIO}`runIO`.
Indeed, it is enough to define {anchorName showFileAndDir}`showFileName` and {anchorName showFileAndDir}`showDirName` without using {anchorName runIO}`runIO`:

```anchor showFileAndDir
def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {file}"

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {dir}/"
```

One final operation from the original {anchorName ConfigIO}`ConfigIO` remains to be translated to a use of {anchorName MyReaderT}`ReaderT`: {anchorName locally}`locally`.
The definition can be translated directly to {anchorName MyReaderT}`ReaderT`, but the Lean standard library provides a more general version.
The standard version is called {anchorName MyMonadWithReader}`withReader`, and it is part of a type class called {anchorName MyMonadWithReader}`MonadWithReader`:

```anchor MyMonadWithReader
class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α
```
Just as in {anchorName MonadReader}`MonadReader`, the environment {anchorName MyMonadWithReader}`ρ` is an {anchorName MyMonadWithReader}`outParam`.
The {anchorName exportWithReader}`withReader` operation is exported, so that it doesn't need to be written with the type class name before it:

```anchor exportWithReader
export MonadWithReader (withReader)
```
The instance for {anchorName ReaderTWithReader}`ReaderT` is essentially the same as the definition of {anchorName locally}`locally`:

```anchor ReaderTWithReader
instance : MonadWithReader ρ (ReaderT ρ m) where
  withReader change action :=
    fun cfg => action (change cfg)
```

With these definitions in place, the new version of {anchorName readerTDirTree}`dirTree` can be written:

```anchor readerTDirTree
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← toEntry path with
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← path.readDir
      withReader (·.inDirectory)
        (doList (contents.qsort dirLT).toList fun d =>
          dirTree d.path)
```
Aside from replacing {anchorName locally}`locally` with {anchorName readerTDirTree}`withReader`, it is the same as before.


Replacing the custom {anchorName ConfigIO}`ConfigIO` type with {anchorName MonadMyReaderT}`ReaderT` did not save a large number of lines of code in this section.
However, rewriting the code using components from the standard library does have long-term benefits.
First, readers who know about {anchorName MyReaderT}`ReaderT` don't need to take time to understand the {anchorName ConfigIO}`Monad` instance for {anchorName ConfigIO}`ConfigIO`, working backwards to the meaning of monad itself.
Instead, they can be confident in their initial understanding.
Next, adding further effects to the monad (such as a state effect to count the files in each directory and display a count at the end) requires far fewer changes to the code, because the monad transformers and {anchorName MonadLiftReaderT}`MonadLift` instances provided in the library work well together.
Finally, using a set of type classes included in the standard library, polymorphic code can be written in such a way that it can work with a variety of monads without having to care about details like the order in which the monad transformers were applied.
Just as some functions work in any monad, others can work in any monad that provides a certain type of state, or a certain type of exceptions, without having to specifically describe the _way_ in which a particular concrete monad provides the state or exceptions.

# Exercises
%%%
tag := "reader-io-exercises"
%%%

## Controlling the Display of Dotfiles
%%%
tag := none
%%%

Files whose names begin with a dot character ({lit}`'.'`) typically represent files that should usually be hidden, such as source-control metadata and configuration files.
Modify {lit}`doug` with an option to show or hide filenames that begin with a dot.
This option should be controlled with a {lit}`-a` command-line option.

## Starting Directory as Argument
%%%
tag := none
%%%

Modify {lit}`doug` so that it takes a starting directory as an additional command-line argument.
