import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

#doc (Manual) "Types" =>


Types classify programs based on the values that they can
compute. Types serve a number of roles in a program:

 1. They allow the compiler to make decisions about the in-memory representation of a value.

 2. They help programmers to communicate their intent to others, serving as a lightweight specification for the inputs and outputs of a function.
    The compiler ensures that the program adheres to this specification.

 3. They prevent various potential mistakes, such as adding a number to a string, and thus reduce the number of tests that are necessary for a program.

 4. They help the Lean compiler automate the production of auxiliary code that can save boilerplate.

Lean's type system is unusually expressive.
Types can encode strong specifications like "this sorting function returns a permutation of its input" and flexible specifications like "this function has different return types, depending on the value of its argument".
The type system can even be used as a full-blown logic for proving mathematical theorems.
This cutting-edge expressive power doesn't make simpler types unnecessary, however, and understanding these simpler types is a prerequisite for using the more advanced features.

:::paragraph
Every program in Lean must have a type. In particular, every
expression must have a type before it can be evaluated. In the
examples so far, Lean has been able to discover a type on its own, but
it is sometimes necessary to provide one. This is done using the colon
operator inside parentheses:

{exampleIn Examples.Intro onePlusTwoEval}


Here, {term}`Nat` is the type of _natural numbers_, which are arbitrary-precision unsigned integers.
In Lean, {term}`Nat` is the default type for non-negative integer literals.
This default type is not always the best choice.
In C, unsigned integers underflow to the largest representable numbers when subtraction would otherwise yield a result less than zero.
{term}`Nat`, however, can represent arbitrarily-large unsigned numbers, so there is no largest number to underflow to.
Thus, subtraction on {term}`Nat` returns {term}`zero` when the answer would have otherwise been negative.
For instance,

{exampleIn Examples.Intro oneMinusTwoEval}

evaluates to {exampleInfo}`oneMinusTwoEval` rather than `-1`.
To use a type that can represent the negative integers, provide it directly:

{exampleIn Examples.Intro oneMinusTwoIntEval}

With this type, the result is {exampleInfo}`oneMinusTwoIntEval`, as expected.
:::

:::paragraph
To check the type of an expression without evaluating it, use {kw}`#check` instead of {kw}`#eval`. For instance:


{exampleIn oneMinusTwoIntType}

reports {exampleInfo}`oneMinusTwoIntType` without actually performing the subtraction.
:::

:::paragraph
When a program can't be given a type, an error is returned from both {kw}`#check` and {kw}`#eval`. For instance:

{exampleIn stringAppendList}

outputs

{exampleError stringAppendList}

because the first argument to {term}`String.append` is expected to be a string, but a list of strings was provided instead.
:::
