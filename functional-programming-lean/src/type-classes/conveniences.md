# Additional Conveniences

## Constructor Syntax for Instances

Behind the scenes, type classes are structure types and instances are values of these types.
The only differences are that Lean stores additional information about type classes, such as which parameters are output parameters, and that instances are registered for searching.
While values that have structure types are typically defined using either `⟨...⟩` syntax or with braces and fields, and instances are typically defined using `where`, both syntaxes work for both kinds of definition.

For example, a forestry application might represent trees as follows:
```lean
{{#example_decl Examples/Classes.lean trees}}
```
All three syntaxes are equivalent.

Similarly, type class instances can be defined using all three syntaxes:
```lean
{{#example_decl Examples/Classes.lean Display}}
```

Generally speaking, the `where` syntax should be used for instances, and the curly-brace syntax should be used for structures.
The `⟨...⟩` syntax can be useful when emphasizing that a structure type is very much like a tuple in which the fields happen to be named, but the names are not important at the moment.
However, there are situations where it can make sense to use other alternatives.
In particular, a library might provide a function that constructs an instance value.
Placing a call to this function after `:=` in an instance declaration is the easiest way to use such a function.

## Examples

When experimenting with Lean code, definitions can be more convenient to use than `#eval` or `#check` commands.
First off, definitions don't produce any output, which can help keep the reader's focus on the most interesting output.
Secondly, it's easiest to write most Lean programs by starting with a type signature, allowing Lean to provide more assistance and better error messages while writing the program itself.
On the other hand, `#eval` and `#check` are easiest to use in contexts where Lean is able to determine the type from the provided expression.
Thirdly, `#eval` cannot be used with expressions whose types don't have `ToString` or `Repr` instances, such as functions.
Finally, multi-step `do` blocks, `let`-expressions, and other syntactic forms that take multiple lines are particularly difficult to write with a type annotation in `#eval` or `#check`, simply because the required parenthesization can be difficult to predict.

To work around these issues, Lean supports the explicit indication of examples in a source file.
An example is like a definition without a name.
For instance, a non-empty list of birds commonly found in Copenhagen's green spaces can be written:
```lean
{{#example_decl Examples/Classes.lean birdExample}}
```

Examples may define functions by accepting arguments:
```lean
{{#example_decl Examples/Classes.lean commAdd}}
```
While this creates a function behind the scenes, this function has no name and cannot be called.
Nonetheless, this is useful for demonstrating how a library can be used with arbitrary or unknown values of some given type.
In source files, `example` declarations are best paired with comments that explain how the example illustrates the concepts of the library.

