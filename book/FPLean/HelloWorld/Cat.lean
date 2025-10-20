import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "FelineLib"

example_module Examples.Cat

#doc (Manual) "Worked Example: {lit}`cat`" =>
%%%
tag := "example-cat"
%%%

The standard Unix utility {lit}`cat` takes a number of command-line options, followed by zero or more input files.
If no files are provided, or if one of them is a dash ({lit}`-`), then it takes the standard input as the corresponding input instead of reading a file.
The contents of the inputs are written, one after the other, to the standard output.
If a specified input file does not exist, this is noted on standard error, but {lit}`cat` continues concatenating the remaining inputs.
A non-zero exit code is returned if any of the input files do not exist.

This section describes a simplified version of {lit}`cat`, called {lit}`feline`.
Unlike commonly-used versions of {lit}`cat`, {lit}`feline` has no command-line options for features such as numbering lines, indicating non-printing characters, or displaying help text.
Furthermore, it cannot read more than once from a standard input that's associated with a terminal device.

To get the most benefit from this section, follow along yourself.
It's OK to copy-paste the code examples, but it's even better to type them in by hand.
This makes it easier to learn the mechanical process of typing in code, recovering from mistakes, and interpreting feedback from the compiler.

# Getting Started
%%%
tag := "example-cat-start"
%%%

The first step in implementing {lit}`feline` is to create a package and decide how to organize the code.
In this case, because the program is so simple, all the code will be placed in {lit}`Main.lean`.
The first step is to run {lit}`lake new feline`.
Edit the Lakefile to remove the library, and delete the generated library code and the reference to it from {lit}`Main.lean`.
Once this has been done, {lit}`lakefile.toml` should contain:

```plainFile "feline/1/lakefile.toml"
name = "feline"
version = "0.1.0"
defaultTargets = ["feline"]

[[lean_exe]]
name = "feline"
root = "Main"
```

and {lit}`Main.lean` should contain something like:
```plainFile "feline/1/Main.lean"
def main : IO Unit :=
  IO.println s!"Hello, cats!"
```
Alternatively, running {lit}`lake new feline exe` instructs {lit}`lake` to use a template that does not include a library section, making it unnecessary to edit the file.

Ensure that the code can be built by running {command feline1 "feline/1"}`lake build`.


# Concatenating Streams
%%%
tag := "example-cat-streams"
%%%

Now that the basic skeleton of the program has been built, it's time to actually enter the code.
A proper implementation of {lit}`cat` can be used with infinite IO streams, such as {lit}`/dev/random`, which means that it can't read its input into memory before outputting it.
Furthermore, it should not work one character at a time, as this leads to frustratingly slow performance.
Instead, it's better to read contiguous blocks of data all at once, directing the data to the standard output one block at a time.

The first step is to decide how big of a block to read.
For the sake of simplicity, this implementation uses a conservative 20 kilobyte block.
{anchorName bufsize}`USize` is analogous to {c}`size_t` in C—it's an unsigned integer type that is big enough to represent all valid array sizes.
```module (anchor:=bufsize)
def bufsize : USize := 20 * 1024
```


## Streams
%%%
tag := "streams"
%%%

The main work of {lit}`feline` is done by {anchorName dump}`dump`, which reads input one block at a time, dumping the result to standard output, until the end of the input has been reached.
The end of the input is indicated by {anchorName dump}`read` returning an empty byte array:
```module (anchor:=dump)
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```

The {anchorName dump}`dump` function is declared {anchorTerm dump}`partial`, because it calls itself recursively on input that is not immediately smaller than an argument.
When a function is declared to be partial, Lean does not require a proof that it terminates.
On the other hand, partial functions are also much less amenable to proofs of correctness, because allowing infinite loops in Lean's logic would make it unsound.
However, there is no way to prove that {anchorName dump}`dump` terminates, because infinite input (such as from {lit}`/dev/random`) would mean that it does not, in fact, terminate.
In cases like this, there is no alternative to declaring the function {anchorTerm dump}`partial`.

The type {anchorName dump}`IO.FS.Stream` represents a POSIX stream.
Behind the scenes, it is represented as a structure that has one field for each POSIX stream operation.
Each operation is represented as an IO action that provides the corresponding operation:

```anchor Stream (module := Examples.Cat)
structure Stream where
  flush   : IO Unit
  read    : USize → IO ByteArray
  write   : ByteArray → IO Unit
  getLine : IO String
  putStr  : String → IO Unit
  isTty   : BaseIO Bool
```

The type {anchorName Stream (module:=Examples.Cat)}`BaseIO` is a variant of {anchorName Stream (module:=Examples.Cat)}`IO` that rules out run-time errors.
The Lean compiler contains {anchorName Stream (module:=Examples.Cat)}`IO` actions (such as {anchorName dump}`IO.getStdout`, which is called in {anchorName dump}`dump`) to get streams that represent standard input, standard output, and standard error.
These are {anchorName Stream (module:=Examples.Cat)}`IO` actions rather than ordinary definitions because Lean allows these standard POSIX streams to be replaced in a process, which makes it easier to do things like capturing the output from a program into a string by writing a custom {anchorName dump}`IO.FS.Stream`.

The control flow in {anchorName dump}`dump` is essentially a {lit}`while` loop.
When {anchorName dump}`dump` is called, if the stream has reached the end of the file, {anchorTerm dump}`pure ()` terminates the function by returning the constructor for {anchorName dump}`Unit`.
If the stream has not yet reached the end of the file, one block is read, and its contents are written to {anchorName dump}`stdout`, after which {anchorName dump}`dump` calls itself directly.
The recursive calls continue until {anchorTerm dump}`stream.read` returns an empty byte array, which indicates the end of the file.

When an {kw}`if` expression occurs as a statement in a {kw}`do`, as in {anchorName dump}`dump`, each branch of the {kw}`if` is implicitly provided with a {kw}`do`.
In other words, the sequence of steps following the {kw}`else` are treated as a sequence of {anchorName dump}`IO` actions to be executed, just as if they had a {kw}`do` at the beginning.
Names introduced with {kw}`let` in the branches of the {kw}`if` are visible only in their own branches, and are not in scope outside of the {kw}`if`.

There is no danger of running out of stack space while calling {anchorName dump}`dump` because the recursive call happens as the very last step in the function, and its result is returned directly rather than being manipulated or computed with.
This kind of recursion is called _tail recursion_, and it is described in more detail {ref "tail-recursion"}[later in this book].
Because the compiled code does not need to retain any state, the Lean compiler can compile the recursive call to a jump.

If {lit}`feline` only redirected standard input to standard output, then {anchorName dump}`dump` would be sufficient.
However, it also needs to be able to open files that are provided as command-line arguments and emit their contents.
When its argument is the name of a file that exists, {anchorName fileStream}`fileStream` returns a stream that reads the file's contents.
When the argument is not a file, {anchorName fileStream}`fileStream` emits an error and returns {anchorName fileStream}`none`.
```module (anchor:=fileStream)
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))
```

Opening a file as a stream takes two steps.
First, a file handle is created by opening the file in read mode.
A Lean file handle tracks an underlying file descriptor.
When there are no references to the file handle value, a finalizer closes the file descriptor.
Second, the file handle is given the same interface as a POSIX stream using {anchorName fileStream}`IO.FS.Stream.ofHandle`, which fills each field of the {anchorName Names}`Stream` structure with the corresponding {anchorName fileStream}`IO` action that works on file handles.

## Handling Input
%%%
tag := "handling-input"
%%%

The main loop of {lit}`feline` is another tail-recursive function, called {anchorName process}`process`.
In order to return a non-zero exit code if any of the inputs could not be read, {anchorName process}`process` takes an argument {anchorName process}`exitCode` that represents the current exit code for the whole program.
Additionally, it takes a list of input files to be processed.
```module (anchor:=process)
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args
```

Just as with {kw}`if`, each branch of a {kw}`match` that is used as a statement in a {kw}`do` is implicitly provided with its own {kw}`do`.

There are three possibilities.
One is that no more files remain to be processed, in which case {anchorName process}`process` returns the error code unchanged.
Another is that the specified filename is {anchorTerm process}`"-"`, in which case {anchorName process}`process` dumps the contents of the standard input and then processes the remaining filenames.
The final possibility is that an actual filename was specified.
In this case, {anchorName process}`fileStream` is used to attempt to open the file as a POSIX stream.
Its argument is encased in {lit}`⟨ ... ⟩` because a {anchorName Names}`FilePath` is a single-field structure that contains a string.
If the file could not be opened, it is skipped, and the recursive call to {anchorName process}`process` sets the exit code to {anchorTerm process}`1`.
If it could, then it is dumped, and the recursive call to {anchorName process}`process` leaves the exit code unchanged.

{anchorName process}`process` does not need to be marked {kw}`partial` because it is structurally recursive.
Each recursive call is provided with the tail of the input list, and all Lean lists are finite.
Thus, {anchorName process}`process` does not introduce any non-termination.

## Main
%%%
tag := "example-cat-main"
%%%

The final step is to write the {anchorName main}`main` action.
Unlike prior examples, {anchorName main}`main` in {lit}`feline` is a function.
In Lean, {anchorName main}`main` can have one of three types:
 * {anchorTerm Names}`main : IO Unit` corresponds to programs that cannot read their command-line arguments and always indicate success with an exit code of {anchorTerm Names}`0`,
 * {anchorTerm Names}`main : IO UInt32` corresponds to {c}`int main(void)` in C, for programs without arguments that return exit codes, and
 * {anchorTerm Names}`main : List String → IO UInt32` corresponds to {c}`int main(int argc, char **argv)` in C, for programs that take arguments and signal success or failure.

If no arguments were provided, {lit}`feline` should read from standard input as if it were called with a single {anchorTerm main}`"-"` argument.
Otherwise, the arguments should be processed one after the other.
```module (anchor:=main)
def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
```

# Meow!
%%%
tag := "example-cat-running"
%%%

:::paragraph
To check whether {lit}`feline` works, the first step is to build it with {command feline2 "feline/2"}`lake build`.
First off, when called without arguments, it should emit what it receives from standard input.
Check that
```command feline2 "feline/2" (shell := true)
echo "It works!" | lake exe feline
```
emits {commandOut feline2}`echo "It works!" | lake exe feline`.
:::

:::paragraph
Secondly, when called with files as arguments, it should print them.
If the file {lit}`test1.txt` contains
```plainFile "feline/2/test1.txt"
It's time to find a warm spot
```

and {lit}`test2.txt` contains
```plainFile "feline/2/test2.txt"
and curl up!
```

then the command

{command feline2 "feline/2" "lake exe feline test1.txt test2.txt"}

should emit
```commandOut feline2 "lake exe feline test1.txt test2.txt"
It's time to find a warm spot
and curl up!
```
:::

Finally, the {lit}`-` argument should be handled appropriately.
```command feline2 "feline/2" (shell := true)
echo "and purr" | lake exe feline test1.txt - test2.txt
```

should yield
```commandOut feline2 "echo \"and purr\" | lake exe feline test1.txt - test2.txt"
It's time to find a warm spot
and purr
and curl up!
```


# Exercise
%%%
tag := "example-cat-exercise"
%%%

Extend {lit}`feline` with support for usage information.
The extended version should accept a command-line argument {lit}`--help` that causes documentation about the available command-line options to be written to standard output.
