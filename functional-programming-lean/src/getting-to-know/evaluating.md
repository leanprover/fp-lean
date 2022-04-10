Lean is a pure functional programming language. Typical programs accomplish
their computation by substituting for variables and then calculating
the resulting value, rather than by sequentially mutating a shared
heap. In fact, evaluating expressions _cannot_ have side effects at
all.

To evaluate an expression, write `#eval` before it in your editor,
which will then report the result back. Typically, the result is found
by putting the cursor or mouse pointer over `#eval`. For instance,

```Lean
#eval {{#example_in Examples/Intro.lean three}}
```
yields the value `{{#example_out Examples/Intro.lean three}}`, and

```Lean
#eval {{#example_in Examples/Intro.lean stringAppend}}
```

yields the value `{{#example_out Examples/Intro.lean stringAppend}}`.
