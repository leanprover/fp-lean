# Step By Step

A `do` block can be executed one line at a time.
Start with the program from the prior section:
```Lean
{{#include ../../../examples/hello-name/HelloName.lean:block1}}
```

## Standard IO

The first line is `{{#include ../../../examples/hello-name/HelloName.lean:line1}}`, while the remainder is:
```Lean
{{#include ../../../examples/hello-name/HelloName.lean:block2}}
```
To execute a `let` statement that uses a `←`, start by evaluating the expression to the right of the arrow (in this case, `IO.getStdIn`).
Because this expression is just a variable, its value is looked up.
The resulting value is a built-in primitive `IO` action.
The next step is to execute the resulting `IO` action.
Executing this action results in a value that represents the standard input stream, which has type `IO.FS.Stream`.
The result of executing the `IO` action is then associated with the name to the left of the arrow (here `stdin`) for the remainder of the `do` block.

Executing the second line, `{{#include ../../../examples/hello-name/HelloName.lean:line2}}`, proceeds similarly.
First, the expression `IO.getStdout` is evaluated, yielding an `IO` action that will return the standard output.
Next, this action is executed, actually returning the standard output.
Finally, this value is associated with the name `stdout` for the remainder of the `do` block.

## Asking a Question

Now that `stdin` and `stdout` have been found, the remainder of the block consists of a question and an answer:
```Lean
{{#include ../../../examples/hello-name/HelloName.lean:block3}}
```

The first statement in the block, `{{#include ../../../examples/hello-name/HelloName.lean:line3}}`, consists of an expression.
To execute a expression, it is first evaluated.
In this case, `IO.FS.Stream.putStrLn` has type `IO.FS.Stream → String → IO Unit`.
This means that it is a function that accepts a stream and a string, returning an `IO` action.
The expression uses [accessor notation](../getting-to-know/structures.md#behind-the-scenes) for a function call.
This function is applied to two arguments: the standard output stream and a string.
The value of the expression is an `IO` action that will write the string and a newline character to the output stream.
Having found this value, the next step is to execute it, which causes the string and newline to be output.
Statements that consist only of expressions do not introduce any new variables.

The next statement in the block is `{{#include ../../../examples/hello-name/HelloName.lean:line4}}`.
`IO.FS.Stream.getLine` has type `IO.FS.Stream → IO String`, which means that it is a function from a stream to an `IO` action that will return a string.
Once again, this is an example of accessor notation.
This `IO` action is executed, and the program waits until the user has typed a complete line of input.
Assume the user writes "`David`".
The resulting line (`"David\n"`) is associated with `input`, where `\n` is the newline character.

```Lean
{{#include ../../../examples/hello-name/HelloName.lean:block5}}
```

The next line, `{{#include ../../../examples/hello-name/HelloName.lean:line5}}`, is a `let` statement that uses `:=` instead of `←`.
This means that the expression will be evaluated, but the result need not be an `IO` action and will not be executed.
In this case, `String.dropRightWhile` takes a string and a predicate over characters and returns a new string from which all the characters that satisfy the predicate have been removed.
In this case, all whitespace characters (including the newline) are removed from the right side of the input string, resulting in `"David"`, which is associated with `name` for the remainder of the block.
In a `do` block, `let` statements that use `:=` are essentially the same as `let` expressions in ordinary Lean code, with the only difference being that the local name is available in any number of statements rather than just in one expression.

**TODO** - show some examples of the function `dropRightWhile`



## Greeting the User

All that remains to be executed in the `do` block is a single statement:
```Lean
{{#include ../../../examples/hello-name/HelloName.lean:line6}}
```
The string argument to `putStrLn` is constructed via string interpolation, yielding the string `"Hello, David!"`.
Because this statement is an expression, it is evaluated to yield an `IO` action that will print this string with a newline to standard output.
Once the expression has been evaluated, the resulting `IO` action is executed, resulting in the greeting.

## TODO

 * List of IO actions - show when they are executed!
