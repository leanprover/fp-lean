Types classify programs based on the values that they can
compute. Types serve a number of roles in a program:
 1. They allow the computer to make decisions about the in-memory
    representation of a value.
 2. They allow programmers to communicate their intent to others,
    serving as a lightweight specification for the inputs and outputs
    of a function that the compiler can ensure the program adheres to.
 3. They prevent various potential mistakes, such as adding a number
    to a string, and thus reduce the number of tests that are
    necessary for a program.

Every program in Lean must have a type. In particular, every
expression must have a type before it can be evaluated. In the
examples so far, Lean has been able to discover a type on its own, but
it is sometimes necessary to provide one. This is done using the colon
operator:

```Lean
#eval {{#example_in Examples/Intro.lean onePlusTwoType}}
```

Here, `Nat` is the type of _natural numbers_, arbitrary-precision
unsigned integers. In Lean, `Nat` is the default type for non-negative
integer literals. This default type is not always the best
choice. Because `Nat` can't represent negative numbers, subtraction
returns `0` when the answer would have otherwise been negative. For
instance,

```Lean
#eval {{#example_in Examples/Intro.lean oneMinusTwo}}
```

evaluates to `{{#example_out Examples/Intro.lean oneMinusTwo}}` rather
than `-1`. To use a type that can represent the negative integers,
provide a type:

```Lean
#eval {{#example_in Examples/Intro.lean oneMinusTwoInt}}
```

With this type, the result is `{{#example_out Examples/Intro.lean oneMinusTwoInt}}`, as expected.

To check the type of an expression without evaluating it, use `#check`
instead of `#eval`. For instance:

```Lean
{{#example_in Examples/Intro.lean oneMinusTwoIntType}}
```

reports `{{#example_out Examples/Intro.lean oneMinusTwoIntType}}` without actually performing the subtraction.

When a program can't be given a type, an error is returned from both
`#check` and `#eval`. For instance:

```Lean
{{#example_in Examples/Intro.lean stringAppendList}}
```

returns

```
{{#example_out Examples/Intro.lean stringAppendList}}
```

