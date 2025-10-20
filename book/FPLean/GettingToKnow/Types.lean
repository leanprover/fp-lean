import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "Types" =>
%%%
tag := "getting-to-know-types"
%%%

Types classify programs based on the values that they can
compute. Types serve a number of roles in a program:

 1. They allow the compiler to make decisions about the in-memory representation of a value.

 2. They help programmers to communicate their intent to others, serving as a lightweight specification for the inputs and outputs of a function.
    The compiler ensures that the program adheres to this specification.

 3. They prevent various potential mistakes, such as adding a number to a string, and thus reduce the number of tests that are necessary for a program.

 4. They help the Lean compiler automate the production of auxiliary code that can save boilerplate.

Lean's type system is unusually expressive.
Types can encode strong specifications like “this sorting function returns a permutation of its input” and flexible specifications like “this function has different return types, depending on the value of its argument”.
The type system can even be used as a full-blown logic for proving mathematical theorems.
This cutting-edge expressive power doesn't make simpler types unnecessary, however, and understanding these simpler types is a prerequisite for using the more advanced features.

:::paragraph
Every program in Lean must have a type. In particular, every
expression must have a type before it can be evaluated. In the
examples so far, Lean has been able to discover a type on its own, but
it is sometimes necessary to provide one. This is done using the colon
operator inside parentheses:

```anchor onePlusTwoEval
#eval (1 + 2 : Nat)
```


Here, {anchorName onePlusTwoEval}`Nat` is the type of _natural numbers_, which are arbitrary-precision unsigned integers.
In Lean, {anchorName onePlusTwoEval}`Nat` is the default type for non-negative integer literals.
This default type is not always the best choice.
In C, unsigned integers underflow to the largest representable numbers when subtraction would otherwise yield a result less than zero.
{anchorName onePlusTwoEval}`Nat`, however, can represent arbitrarily-large unsigned numbers, so there is no largest number to underflow to.
Thus, subtraction on {anchorName onePlusTwoEval}`Nat` returns {anchorName Nat}`zero` when the answer would have otherwise been negative.
For instance,

```anchor oneMinusTwoEval
#eval (1 - 2 : Nat)
```

evaluates to {anchorInfo oneMinusTwoEval}`0` rather than {lit}`-1`.
To use a type that can represent the negative integers, provide it directly:

```anchor oneMinusTwoIntEval
#eval (1 - 2 : Int)
```

With this type, the result is {anchorInfo oneMinusTwoIntEval}`-1`, as expected.
:::

:::paragraph
To check the type of an expression without evaluating it, use {kw}`#check` instead of {kw}`#eval`. For instance:

```anchor oneMinusTwoIntType
#check (1 - 2 : Int)
```

reports {anchorInfo oneMinusTwoIntType}`1 - 2 : Int` without actually performing the subtraction.
:::

:::paragraph
When a program can't be given a type, an error is returned from both {kw}`#check` and {kw}`#eval`. For instance:

```anchor stringAppendList
#check String.append ["hello", " "] "world"
```

outputs

```anchorError stringAppendList
Application type mismatch: The argument
  ["hello", " "]
has type
  List String
but is expected to have type
  String
in the application
  String.append ["hello", " "]
```

because the first argument to {anchorName stringAppendList}`String.append` is expected to be a string, but a list of strings was provided instead.
:::
