In Lean, definitions are introduced using the `def` keyword. For instance, to define the name `{{#example_in Examples/Intro.lean helloNameVal}}` to refer to the string `{{#example_out Examples/Intro.lean helloNameVal}}`, write:

```Lean
{{#example_decl Examples/Intro.lean hello}}
```


In Lean, new names are defined using the colon-equal operator`:=`
rather than `=`. This is because `=` is used to describe equalities
between existing expressions, and using two different operators helps
keep these usages different.

In the definition of `{{#example_in Examples/Intro.lean helloNameVal}}`,
`{{#example_out Examples/Intro.lean helloNameVal}}` is simple enough
that Lean is able to determine the definition's type automatically. However,
most definitions are not so simple, so it will usually be necessary to add a
type. This is done using a colon after the name being defined.

```Lean
{{#example_decl Examples/Intro.lean lean}}
```

Now that the names have been defined, they can be used, so
``` Lean
{{#example_in Examples/Intro.lean helloLean}}
```
outputs
``` Lean
{{#example_out Examples/Intro.lean helloLean}}
```

In Lean, defined names may only be used after their definition site.

