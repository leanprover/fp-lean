# Types

Types classify programs based on the values that they can
compute. Types serve a number of roles in a program:

 1. They allow the compiler to make decisions about the in-memory
    representation of a value.

 2. They help programmers to communicate their intent to others,
    serving as a lightweight specification for the inputs and outputs
    of a function that the compiler can ensure the program adheres to.

 3. They prevent various potential mistakes, such as adding a number
    to a string, and thus reduce the number of tests that are
    necessary for a program.

 4. They help the Lean compiler automate the production of auxiliary code that can save boilerplate.

Lean's type system is unusually expressive.
Types can encode strong specifications like "this sorting function returns a permutation of its input" and flexible specifications like "this function has different return types, depending on the value of its argument".
The type system can even be used as a full-blown logic for proving mathematical theorems.
This cutting-edge expressive power doesn't obviate the need for simpler types, however, and understanding these simpler types is a prerequisite for using the more advanced features.

Every program in Lean must have a type. In particular, every
expression must have a type before it can be evaluated. In the
examples so far, Lean has been able to discover a type on its own, but
it is sometimes necessary to provide one. This is done using the colon
operator:

```lean
#eval {{#example_in Examples/Intro.lean onePlusTwoType}}
```

Here, `Nat` is the type of _natural numbers_, which are arbitrary-precision unsigned integers.
In Lean, `Nat` is the default type for non-negative integer literals.
This default type is not always the best choice.
In C, unsigned integers underflow to the largest representable numbers when subtraction would otherwise yield a result less than zero.
`Nat`, however, can represent arbitrarily-large unsigned numbers, so there is no largest number to underflow to.
Thus, subtraction on `Nat` returns `0` when the answer would have otherwise been negative.
For instance,

```lean
#eval {{#example_in Examples/Intro.lean oneMinusTwo}}
```

evaluates to `{{#example_out Examples/Intro.lean oneMinusTwo}}` rather
than `-1`. To use a type that can represent the negative integers,
provide a it directly:

```lean
#eval {{#example_in Examples/Intro.lean oneMinusTwoInt}}
```

With this type, the result is `{{#example_out Examples/Intro.lean oneMinusTwoInt}}`, as expected.

To check the type of an expression without evaluating it, use `#check`
instead of `#eval`. For instance:

```lean
{{#example_in Examples/Intro.lean oneMinusTwoIntType}}
```

reports `{{#example_out Examples/Intro.lean oneMinusTwoIntType}}` without actually performing the subtraction.

When a program can't be given a type, an error is returned from both
`#check` and `#eval`. For instance:

```lean
{{#example_in Examples/Intro.lean stringAppendList}}
```

outputs

```output error
{{#example_out Examples/Intro.lean stringAppendList}}
```

because the second argument to ``String.append`` is expected to be a
string, but a list of strings was provided instead.
