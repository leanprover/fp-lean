# Structures

The first step in writing a program is usually to identify the problem domain's concepts, and then find suitable representations for them in code.
Sometimes, a domain concept is a collection of other, simpler, concepts.
In that case, it can be convenient to group these simpler components together into a single "package", which can then be given a meaningful name.
In Lean, this is done using _structures_, which are analogous to `struct`s in C or Rust and `record`s in C#.

Defining a structure introduces a completely new type to Lean that can't be reduced to any other type.
This is useful because multiple structures might represent different concepts that nonetheless contain the same data.
For instance, a point might be represented using either Cartesian or polar coordinates, each being a pair of floating-point numbers.
Defining separate structures prevents API clients from confusing one for another.

Lean's floating-point number type is called `Float`, and floating-point numbers are written in the usual notation.
```lean
{{#example_in Examples/Intro.lean onePointTwo}}
```
```output info
{{#example_out Examples/Intro.lean onePointTwo}}
```
```lean
{{#example_in Examples/Intro.lean negativeLots}}
```
```output info
{{#example_out Examples/Intro.lean negativeLots}}
```
```lean
{{#example_in Examples/Intro.lean zeroPointZero}}
```
```output info
{{#example_out Examples/Intro.lean zeroPointZero}}
```
When floating point numbers are written with the decimal point, Lean will infer the type `Float`. If they are written without it, then a type annotation may be necessary.
```lean
{{#example_in Examples/Intro.lean zeroNat}}
```
```output info
{{#example_out Examples/Intro.lean zeroNat}}
```

```lean
{{#example_in Examples/Intro.lean zeroFloat}}
```
```output info
{{#example_out Examples/Intro.lean zeroFloat}}
```


A Cartesian point is a structure with two `Float` fields, called `x` and `y`.
This is declared using the `structure` keyword.

```lean
{{#example_decl Examples/Intro.lean Point}}
```

After this declaration, `Point` is a new structure type.
The final line, which says `deriving Repr`, asks Lean to generate code to display values of type `Point`.
This code is used by `#eval` to render the result of evaluation for consumption by programmers, analogous to the `repr` function in Python.
It is also possible to override the compiler's generated display code.

The typical way to create a value of a structure type is to provide values for all of its fields inside of curly braces.
The origin of a Cartesian plane is where `x` and `y` are both zero:

```lean
{{#example_decl Examples/Intro.lean origin}}
```

If the `deriving Repr` line in `Point`'s definition were omitted, then attempting `{{#example_in Examples/Intro.lean PointNoRepr}}` would yield an error similar to that which occurs when omitting a function's argument:
```output error
{{#example_out Examples/Intro.lean PointNoRepr}}
```
That message is saying that the evaluation machinery doesn't know how to communicate the result of evaluation back to the user.

Happily, with `deriving Repr`, the result of `{{#example_in Examples/Intro.lean originEval}}` looks very much like the definition of `origin`.
```output info
{{#example_out Examples/Intro.lean originEval}}
```

Because structures exist to "bundle up" a collection of data, naming it and treating it as a single unit, it is also important to be able to extract the individual fields of a structure.
This is done using dot notation, as in C, Python, or Rust.

```lean
{{#example_in Examples/Intro.lean originx}}
```
```output info
{{#example_out Examples/Intro.lean originx}}
```

```lean
{{#example_in Examples/Intro.lean originy}}
```
```output info
{{#example_out Examples/Intro.lean originy}}
```

This can be used to define functions that take structures as arguments.
For instance, addition of points is performed by adding the underlying coordinate values.
It should be the case that `{{#example_in Examples/Intro.lean addPointsEx}}` yields
```output info
{{#example_out Examples/Intro.lean addPointsEx}}
```
The function itself takes two `Points` as arguments, called `p1` and `p2`.
The resulting point is based on the `x` and `y` fields of both `p1` and `p2`:
```lean
{{#example_decl Examples/Intro.lean addPoints}}
```

Similarly, the distance between two points, which is the square root of the sum of the squares of the differences in their `x` and `y` components, can be written:
```lean
{{#example_decl Examples/Intro.lean distance}}
```
For example, the distance between (1, 2) and (5, -1) is 5:
```lean
{{#example_in Examples/Intro.lean evalDistance}}
```
```output info
{{#example_out Examples/Intro.lean evalDistance}}
```


Multiple structures may have fields with the same names.
For instance, a three-dimensional point datatype may share the fields `x` and `y`, and be instantiated with the same field names:
```lean
{{#example_decl Examples/Intro.lean Point3D}}

{{#example_decl Examples/Intro.lean origin3D}}
```
This means that the structure's expected type must be known in order to use the curly-brace syntax.
If the type is not known, Lean will not be able to instantiate the structure.
For instance,
```lean
{{#example_in Examples/Intro.lean originNoType}}
```
leads to the error
```output error
{{#example_out Examples/Intro.lean originNoType}}
```

As usual, the situation can be remedied by providing a type annotation.
```lean
{{#example_in Examples/Intro.lean originWithAnnot}}
```
```output info
{{#example_out Examples/Intro.lean originWithAnnot}}
```

To make programs more concise, Lean also allows the structure type annotation inside the curly braces.
```lean
{{#example_in Examples/Intro.lean originWithAnnot2}}
```
```output info
{{#example_out Examples/Intro.lean originWithAnnot2}}
```

## Updating Structures

Imagine a function `zeroX` that replaces the `x` field of a `Point` with `0.0`.
In most programming language communities, this sentence would mean that the memory location pointed to by `x` was to be overwritten with a new value.
However, Lean does not have mutable state.
In functional programming communities, what is almost always meant by this kind of statement is that a fresh `Point` is allocated with the `x` field pointing to the new value, and all other fields pointing to the original values from the input.
One way to write `zeroX` is to follow this description literally, filling out the new value for `x` and manually transferring `y`:
```lean
{{#example_decl Examples/Intro.lean zeroXBad}}
```
This style of programming has drawbacks, however.
First off, if a new field is added to a structure, then every site that updates any field at all must be updated, causing maintenance difficulties.
Secondly, if the structure contains multiple fields with the same type, then there is a real risk of copy-paste coding leading to field contents being duplicated or switched.
Finally, the program becomes long and bureaucratic.

Lean provides a convenient syntax for replacing some fields in a structure while leaving the others alone.
This is done by using the `with` keyword in a structure initialization.
The source of unchanged fields occurs before the `with`, and the new fields occur after.
For instance, `zeroX` can be written with only the new `x` value:

```lean
{{#example_decl Examples/Intro.lean zeroX}}
```

Remember that this structure update syntax does not modify existing values—it creates new values that share some fields with old values.
For instance, given the point `fourAndThree`:
```lean
{{#example_decl Examples/Intro.lean fourAndThree}}
```
evaluating it, then evaluating an update of it using `zeroX`, then evaluating it again yields the original value:
```lean
{{#example_in Examples/Intro.lean fourAndThreeEval}}
```
```output info
{{#example_out Examples/Intro.lean fourAndThreeEval}}
```
```lean
{{#example_in Examples/Intro.lean zeroXFourAndThreeEval}}
```
```output info
{{#example_out Examples/Intro.lean zeroXFourAndThreeEval}}
```
```lean
{{#example_in Examples/Intro.lean fourAndThreeEval}}
```
```output info
{{#example_out Examples/Intro.lean fourAndThreeEval}}
```

One consequence of the fact that structure updates do not modify the original structure is that it becomes easier to reason about cases where the new value is computed from the old one.
All references to the old structure continue to refer to the same field values in all of the new values provided.




## Behind the Scenes

Every structure has a _constructor_.
Here, the term "constructor" may be a source of confusion.
Unlike constructors in languages such as Java or Python, constructors in Lean are not arbitrary code to be run when a datatype is initialized.
Instead, constructors simply gather the data to be stored in the newly-allocated data structure.
It is not possible to provide a custom constructor that pre-processes data or rejects invalid arguments.
This is really a case of the word "constructor" having different, but related, meanings in the two contexts.


By default, the constructor for a structure named `S` is named `S.mk`.
Here, `S` is a namespace qualifier, and `mk` is the name of the constructor itself.
Instead of using curly-brace initialization syntax, the constructor can also be applied directly.
```lean
{{#example_in Examples/Intro.lean checkPointMk}}
```
However, this is not generally considered to be good Lean style, and Lean even returns its feedback using the standard structure initializer syntax.
```output info
{{#example_out Examples/Intro.lean checkPointMk}}
```

Constructors have function types, which means they can be used anywhere that a function is expected.
For instance, `Point.mk` is a function that accepts two `Float`s (respectively `x` and `y`) and returns a new `Point`.
```lean
{{#example_in Examples/Intro.lean Pointmk}}
```
```output info
{{#example_out Examples/Intro.lean Pointmk}}
```
To override a structure's constructor name, write it with two colons at the beginning.
For instance, to use `Point.point` instead of `Point.mk`, write:
```lean
{{#example_decl Examples/Intro.lean PointCtorName}}
```

In addition to the constructor, an accessor function is defined for each field of a structure.
These have the same name as the field, in the structure's namespace.
For `Point`, accessor functions `Point.x` and `Point.y` are generated.
```lean
{{#example_in Examples/Intro.lean Pointx}}
```
```output info
{{#example_out Examples/Intro.lean Pointx}}
```

```lean
{{#example_in Examples/Intro.lean Pointy}}
```
```output info
{{#example_out Examples/Intro.lean Pointy}}
```

In fact, just as the curly-braced structure construction syntax is converted to a call to the structure's constructor behind the scenes, the syntax `p1.x` in the prior definition of `addPoints` is converted into a call to the `Point.x` accessor.
That is, `{{#example_in Examples/Intro.lean originx}}` and `{{#example_in Examples/Intro.lean originx1}}` both yield
```output info
{{#example_out Examples/Intro.lean originx1}}
```

Accessor dot notation is usable with more than just structure fields.
It can also be used for functions that take any number of arguments.
More generally, accessor notation has the form `TARGET.f ARG1 ARG2 ...`.
If `TARGET` has type `T`, the function named `T.f` is called.
`TARGET` becomes its leftmost argument of type `T`, which is often but not always the first one, and `ARG1 ARG2 ...` are provided in order as the remaining arguments.
For instance, `String.append` can be invoked from a string with accessor notation, even though `String` is not a structure with an `append` field.
```lean
{{#example_in Examples/Intro.lean stringAppendDot}}
```
```output info
{{#example_out Examples/Intro.lean stringAppendDot}}
```
In that example, `TARGET` represents `"one string"` and `ARG1` represents `" and another"`.

The function `Point.modifyBoth` (that is, `modifyBoth` defined in the `Point` namespace) applies a function to both fields in a `Point`:
```lean
{{#example_decl Examples/Intro.lean modifyBoth}}
```
Even though the `Point` argument comes after the function argument, it can be used with dot notation as well:
```lean
{{#example_in Examples/Intro.lean modifyBothTest}}
```
```output info
{{#example_out Examples/Intro.lean modifyBothTest}}
```
In this case, `TARGET` represents `fourAndThree`, while `ARG1` is `Float.floor`.
This is because the target of the accessor notation is used as the first argument in which the type matches, not necessarily the first argument.

## Exercises

 * Define a structure named `RectangularPrism` that contains the height, width, and depth of a rectangular prism, each as a `Float`.
 * Define a function named `volume : RectangularPrism → Float` that computes the volume of a rectangular prism.
 * Define a structure named `Segment` that represents a line segment by its endpoints, and define a function `length : Segment → Float` that computes the length of a line segment. `Segment` should have at most two fields.
 * Which names are introduced by the declaration of `RectangularPrism`?
 * Which names are introduced by the following declarations of `Hamster` and `Book`? What are their types?

```lean
{{#example_decl Examples/Intro.lean Hamster}}
```

```lean
{{#example_decl Examples/Intro.lean Book}}
```
