import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "Evaluating Expressions" =>
%%%
tag := "evaluating"
%%%


The most important thing to understand as a programmer learning Lean is how evaluation works.
Evaluation is the process of finding the value of an expression, just as one does in arithmetic.
For instance, the value of $`15 - 6` is $`9` and the value of $`2 × (3 + 1)` is $`8`.
To find the value of the latter expression, $`3 + 1` is first replaced by $`4`, yielding $`2 × 4`, which itself can be reduced to $`8`.
Sometimes, mathematical expressions contain variables: the value of $`x + 1` cannot be computed until we know what the value of $`x` is.
In Lean, programs are first and foremost expressions, and the primary way to think about computation is as evaluating expressions to find their values.

Most programming languages are _imperative_, where a program consists of a series of statements that should be carried out in order to find the program's result.
Programs have access to mutable memory, so the value referred to by a variable can change over time.
In addition to mutable state, programs may have other side effects, such as deleting files, making outgoing network connections,
throwing or catching exceptions, and reading data from a database.
“Side effects” is essentially a catch-all term for describing things that may happen in a program that don't follow the model of evaluating mathematical expressions.

In Lean, however, programs work the same way as mathematical expressions.
Once given a value, variables cannot be reassigned. Evaluating an expression cannot have side effects.
If two expressions have the same value, then replacing one with the other will not cause the program to compute a different result.
This does not mean that Lean cannot be used to write {lit}`Hello, world!` to the console, but performing I/O is not a core part of the experience of using Lean in the same way.
Thus, this chapter focuses on how to evaluate expressions interactively with Lean, while the next chapter describes how to write, compile, and run the {lit}`Hello, world!` program.

:::paragraph
To ask Lean to evaluate an expression, write {kw}`#eval` before it in your editor, which will then report the result back.
Typically, the result is found by putting the cursor or mouse pointer over {kw}`#eval`.
For instance,

```anchor threeEval
#eval 1 + 2
```

yields the value

```anchorInfo threeEval
3
```

:::

:::paragraph
Lean obeys the ordinary rules of precedence and associativity for
arithmetic operators. That is,

```anchor orderOfOperations
#eval 1 + 2 * 5
```

yields the value {anchorInfo orderOfOperations}`11` rather than {anchorInfo orderOfOperationsWrong}`15`.

:::

:::paragraph
While both ordinary mathematical notation and the majority of programming languages use parentheses (e.g. {lit}`f(x)`) to apply a function to its arguments, Lean simply writes the function next to its arguments (e.g. {lit}`f x`).
Function application is one of the most common operations, so it pays to keep it concise.
Rather than writing

```
#eval String.append("Hello, ", "Lean!")
```

to compute {anchorInfo stringAppendHello}`"Hello, Lean!"`, one would instead write

```anchor stringAppendHello
#eval String.append "Hello, " "Lean!"
```

where the function's two arguments are simply written next to it with spaces.
:::


:::paragraph
Just as the order-of-operations rules for arithmetic demand parentheses in the expression {anchorTerm orderOfOperationsWrong}`(1 + 2) * 5`, parentheses are also necessary when a function's argument is to be computed via another function call.
For instance, parentheses are required in

```anchor stringAppendNested
#eval String.append "great " (String.append "oak " "tree")
```

because otherwise the second {moduleTerm (anchor := stringAppendNested)}`String.append` would be interpreted as an argument to the first, rather than as a function being passed {moduleTerm (anchor := stringAppendNested)}`"oak "` and {moduleTerm (anchor := stringAppendNested)}`"tree"` as arguments.
The value of the inner {anchorTerm stringAppendNested}`String.append` call must be found first, after which it can be appended to {moduleTerm (anchor := stringAppendNested)}`"great "`, yielding the final value {anchorInfo stringAppendNested}`"great oak tree"`.
:::

:::paragraph
Imperative languages often have two kinds of conditional: a conditional _statement_ that determines which instructions to carry out based on a Boolean value, and a conditional _expression_ that determines which of two expressions to evaluate based on a Boolean value.
For instance, in C and C++, the conditional statement is written using {c}`if` and {c}`else`, while the conditional expression is written with a ternary operator in which {c}`?` and {c}`:` separate the condition from the branches.
In Python, the conditional statement begins with {python}`if`, while the conditional expression puts {python}`if` in the middle.
Because Lean is an expression-oriented functional language, there are no conditional statements, only conditional expressions.
They are written using {kw}`if`, {kw}`then`, and {kw}`else`.
For example,

```anchorEvalStep stringAppend 0
String.append "it is " (if 1 > 2 then "yes" else "no")
```

evaluates to

```anchorEvalStep stringAppend 1
String.append "it is " (if false then "yes" else "no")
```

which evaluates to

```anchorEvalStep stringAppend 2
String.append "it is " "no"
```

which finally evaluates to {anchorEvalStep stringAppend 3}`"it is no"`.


:::


:::paragraph
For the sake of brevity, a series of evaluation steps like this will sometimes be written with arrows between them:

```anchorEvalSteps stringAppend
String.append "it is " (if 1 > 2 then "yes" else "no")
===>
String.append "it is " (if false then "yes" else "no")
===>
String.append "it is " "no"
===>
"it is no"
```
:::


# Messages You May Meet
%%%
tag := "evaluating-messages"
%%%

:::paragraph
Asking Lean to evaluate a function application that is missing an argument will lead to an error message.
In particular, the example

```anchor stringAppendReprFunction
#eval String.append "it is "
```

yields a quite long error message:

```anchorError stringAppendReprFunction
could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  String → String
```

:::

This message occurs because Lean functions that are applied to only some of their arguments return new functions that are waiting for the rest of the arguments.
Lean cannot display functions to users, and thus returns an error when asked to do so.


# Exercises
%%%
tag := "evaluating-exercises"
%%%

What are the values of the following expressions? Work them out by hand,
then enter them into Lean to check your work.

 * {anchorTerm evalEx}`42 + 19`
 * {anchorTerm evalEx}`String.append "A" (String.append "B" "C")`
 * {anchorTerm evalEx}`String.append (String.append "A" "B") "C"`
 * {anchorTerm evalEx}`if 3 == 3 then 5 else 7`
 * {anchorTerm evalEx}`if 3 == 4 then "equal" else "not equal"`
