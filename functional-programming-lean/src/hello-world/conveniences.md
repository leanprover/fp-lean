# Additional Conveniences


## Nested Actions

Many of the functions in `feline` exhibit a repetitive pattern in which an `IO` action's result is given a name, and then used immediately and only once.
For instance, in `dump`:
```Lean
{{#include ../../../examples/feline/2/Main.lean:dump}}
```
the pattern occurs twice:
```Lean
{{#include ../../../examples/feline/2/Main.lean:isEofBind}}
```
and
```Lean
{{#include ../../../examples/feline/2/Main.lean:bufBind}}
```
Similarly, `fileStream` contains the following snippet:
```Lean
{{#include ../../../examples/feline/2/Main.lean:fileExistsBind}}
```

When Lean is compiling a `do` block, expressions that consist of a left arrow immediately under parentheses are lifted to the nearest enclosing `do`, and their results are bound to a unique name.
This unique name replaces the origin of the expression.
This means that `dump` can also be written as follows:
```Lean
{{#example_decl Examples/Cat.lean dump}}
```
This version of `dump` avoids introducing names that are used only once, which can greatly simplify a program.
`IO` actions that Lean lifts from a nested expression context are called _nested actions_.

`fileStream` can be simplified using the same technique:
```Lean
{{#example_decl Examples/Cat.lean fileStream}}
```
In this case, the local name of `handle` could also have been eliminated using nested actions, but the resulting expression would have been long and complicated.
Even though it's often good style to use nested actions, it can still sometimes be helpful to name intermediate results.

It is important to remember, however, that nested actions are only a shorter notation for `IO` actions that occur in a surrounding `do` block.
The side effects that are involved in executing them still occur in the same order, and execution of side effects is not interspersed with the evaluation of expressions.
For an example of where this might be confusing, consider the following helper definitions that return data after announcing to the world that they have been executed:
```Lean
{{#example_decl Examples/Cat.lean getNumA}}

{{#example_decl Examples/Cat.lean getNumB}}
```
These definitions are intended to stand in for more complicated `IO` code that might validate user input, read a database, or open a file.

A program that prints `0` when number A is five, or number `B` otherwise, can be written as follows:
```Lean
{{#example_decl Examples/Cat.lean testEffects}}
```
However, this program probably has more side effects (such as prompting for user input or reading a database) than was intended.
The definition of `getNumA` makes it clear that it will always return `5`, and thus the program should not read number B.
However, running the program results in the following output:
```Lean info
{{#example_out Examples/Cat.lean runTest}}
```
`getNumB` was executed because `test` is equivalent to this definition:
```Lean
{{#example_decl Examples/Cat.lean testEffectsExpanded}}
```
This is due to the rule that nested actions are lifted to the _closest enclosing_ `do` block.
The branches of the `if` were not implicitly wrapped in `do` blocks because the `if` is not _immediately_ under a `do`.
Indeed, they could not be wrapped this way, because the type of the conditional expression is `Nat`, not `IO Nat`.

## Flexible Layouts for `do`

In Lean, `do` expressions are whitespace-sensitive.
Each `IO` action or local binding in the `do` is expected to start on its own line, and they should all have the same indentation.
Almost all uses of `do` should be written this way.
In some rare contexts, however, manual control over whitespace and indentation may be necessary, or it may be convenient to have multiple small actions on a single line.
In these cases, newlines can be replaced with a semicolon and indentation can be replaced with curly braces.

For instance, all of the following programs are equivalent:
```Lean
{{#example_decl Examples/Cat.lean helloOne}}

{{#example_decl Examples/Cat.lean helloTwo}}

{{#example_decl Examples/Cat.lean helloThree}}
```

Idiomatic Lean code uses curly braces with `do` very rarely.

## Running `IO` Actions With `#eval`

Lean's `#eval` command can be used to execute `IO` actions, rather than just evaluating them.
Normally, adding a `#eval` command to a Lean file causes Lean to evaluate the provided expression, convert the resulting value to a string, and provide that string as a tooltip and in the info window.
Rather than failing because `IO` actions can't be converted to strings, `#eval` executes them, carrying out their side effects.
If the result of execution is the `Unit` value `()`, then no result string is shown, but if it is a type that can be converted to a string, then Lean displays the resulting value.

This means that, given the prior definitions of `countdown` and `runActions`, 
```Lean
{{#example_in Examples/HelloWorld.lean evalDoesIO}}
```
displays
```Lean info
{{#example_out Examples/HelloWorld.lean evalDoesIO}}
```
This is the output produced by running the `IO` action, rather than some opaque representation of the action itself.
In other words, for `IO` actions, `#eval` both _evaluates_ the provided expression and _executes_ the resulting action value.

Quickly testing `IO` actions with `#eval` can be much more convenient that compiling and running whole programs.
However, there are some limitations.
For instance, reading from standard input simply returns empty input.
Additionally, the `IO` action is re-executed whenever Lean needs to update the diagnostic information that it provides to users, and this can happen at unpredictable times.
An action that reads and writes files, for instance, may do so at inconvenient times.
