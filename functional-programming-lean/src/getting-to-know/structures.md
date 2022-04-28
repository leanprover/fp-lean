
The first step in writing a program is usually to identify the problem domain's concepts, and then find suitable representations for them in code.
Sometimes, a domain concept is a collection of other, simpler, concepts.
In that case, it can be convenient to group these simpler components together into a single "package", which can then be given a meaningful name.
In Lean, this is done using _structures_, which are analogous to `struct`s in C or Rust.

Defining a structure introduces a completely new type to Lean that can't be reduced to any other type.
This is useful because multiple structures might represent different concepts that nonetheless contain the same data.
For instance, a point might be represented using either Cartesian or polar coordinates, each being a pair of floating-point numbers.
Defining separate structures prevents API clients from confusing one for another.

Lean's floating-point number type is called `Float`, and floating-point numbers are written in the usual notation.
```Lean
{{#example_in Examples/Intro.lean onePointTwo}}
```
```Lean info
{{#example_out Examples/Intro.lean onePointTwo}}
```
```Lean
{{#example_in Examples/Intro.lean negativeLots}}
```
```Lean info
{{#example_out Examples/Intro.lean negativeLots}}
```
```Lean
{{#example_in Examples/Intro.lean zeroPointZero}}
```
```Lean info
{{#example_out Examples/Intro.lean zeroPointZero}}
```
When floating point numbers are written with the decimal point, Lean will infer the type `Float`, while if they are written without it, then a type annotation may be necessary.
```Lean
{{#example_in Examples/Intro.lean zeroNat}}
```
```Lean info
{{#example_out Examples/Intro.lean zeroNat}}
```

```Lean
{{#example_in Examples/Intro.lean zeroFloat}}
```
```Lean info
{{#example_out Examples/Intro.lean zeroFloat}}
```


A Cartesian point is a structure with two `Float` fields, called `x` and `y`.
This is declared using the `structure` keyword.

```Lean
{{#example_decl Examples/Intro.lean Point}}
```

After this declaration, `Point` is a new structure type.
The final line, which says `deriving Repr`, asks Lean to generate code to display values of type `Point`.
This code is used by `#eval` to render the result of evaluation for human consumption, analogous to the `repr` functions in Python and Rust.

The typical way to create a instance of a structure type is to provide values for all of its fields inside of curly braces.
The origin of a Cartesian plane is where both `x` and `y` are both zero:

```Lean
{{#example_decl Examples/Intro.lean origin}}
```

If the `deriving Repr` line in `Point`'s definition were omitted, then attempting `{{#example_in Examples/Intro.lean PointNoRepr}}` would yield an error:
```Lean error
{{#example_out Examples/Intro.lean PointNoRepr}}
```
That message is saying that the evaluation machinery doesn't know how to communicate the result of evaluation back to the user.

Happily, with `deriving Repr`, the result of `{{#example_in Examples/Intro.lean originEval}}` looks very much like the definition of `origin`.
```Lean info
{{#example_out Examples/Intro.lean originEval}}
```

Because structures exist to "bundle up" a collection of data, naming it and treating it as a single unit, it is also important to be able to extract the individual fields of a structure.
This is done using dot notation, as in C, Python, or Rust.

```Lean
{{#example_in Examples/Intro.lean originx}}
```
```Lean info
{{#example_out Examples/Intro.lean originx}}
```

```Lean
{{#example_in Examples/Intro.lean originy}}
```
```Lean info
{{#example_out Examples/Intro.lean originy}}
```

This can be used to define functions that take structures as arguments.
For instance, addition of points is performed by adding the underlying points.
It should be the case that `{{#example_in Examples/Intro.lean addPointsEx}}` yields
```Lean info
{{#example_out Examples/Intro.lean addPointsEx}}
```
The function itself takes two `Points` as arguments, called `p1` and `p2`.
The resulting point is based on the `x` and `y` fields of both `p1` and `p2`:
```Lean
{{#example_decl Examples/Intro.lean addPoints}}
```

Similarly, the distance between two points, which is the square root of the sum of the squares of the differences in their `x` and `y` components, can be written:
```Lean
{{#example_decl Examples/Intro.lean distance}}
```


Multiple structures may have fields with the same names.
For instance, a three-dimensional point datatype may share the fields `x` and `y`, and be instantiated with the same field names:
```Lean
{{#example_decl Examples/Intro.lean Point3D}}

{{#example_decl Examples/Intro.lean origin3D}}
```
This means that the structure's expected type must be known in order to use the curly-brace syntax.
If the type is not known, Lean will not be able to instantiate the structure.
For instance,
```Lean
{{#example_in Examples/Intro.lean originNoType}}
```
leads to the error
```Lean error
{{#example_out Examples/Intro.lean originNoType}}
```

As usual, the situation can be remedied by providing a type annotation.
```Lean
{{#example_in Examples/Intro.lean originWithAnnot}}
```
```Lean info
{{#example_out Examples/Intro.lean originWithAnnot}}
```

To make programs more concise, Lean also allows the structure type annotation inside the curly braces.
```Lean
{{#example_in Examples/Intro.lean originWithAnnot2}}
```
```Lean info
{{#example_out Examples/Intro.lean originWithAnnot2}}
```

# Behind the Scenes

Behind the scenes, every structure has a _constructor_.
Here, the term "constructor" may be a source of confusion.
Unlike constructors in languages such as Java or Python, constructors in Lean are not arbitrary code to be run when a datatype is initialized.
Instead, constructors simply gather the data to be stored in the newly-allocated data structure.
It is not possible to provide a custom constructor that pre-processes data or rejects invalid arguments.
This is really a case of the word "constructor" having different, but related, meanings in the two contexts.


By default, the constructor for a structure named `S` is named `S.mk`.
Here, `S` is a namespace qualifier, and `mk` is the name of the constructor itself.
Instead of using curly-brace initialization syntax, the constructor can also be applied directly.
```Lean
{{#example_in Examples/Intro.lean checkPointMk}}
```
However, this is not generally considered to be good Lean style, and Lean even returns its feedback using the standard structure initializer syntax.
```Lean info
{{#example_out Examples/Intro.lean checkPointMk}}
```

Constructors have function types, which means that they can be used anywhere that a function is expected.
For instance, `Point.mk` is a function that accepts two `Float`s (respectively `x` and `y`) and returns a new `Point`.
```Lean
{{#example_in Examples/Intro.lean Pointmk}}
```
```Lean info
{{#example_out Examples/Intro.lean Pointmk}}
```
To override a structure's constructor name, write it with two colons at the beginning.
For instance, to use `Point.point` instead of `Point.mk`, write:
```Lean
{{#example_decl Examples/Intro.lean PointCtorName}}
```

In addition to the constructor, an accessor function is defined for each field of a structure.
These have the same name as the field, in the structure's namespace.
For `Point`, accessor functions `Point.x` and `Point.y` are generated.
```Lean
{{#example_in Examples/Intro.lean Pointx}}
```
```Lean info
{{#example_out Examples/Intro.lean Pointx}}
```

```Lean
{{#example_in Examples/Intro.lean Pointy}}
```
```Lean info
{{#example_out Examples/Intro.lean Pointy}}
```

In fact, just as the curly-braced structure construction syntax is converted to a call to the structure's constructor behind the scenes, the syntax `p1.x` in the prior definition of `addPoints` is converted into a call to the `Point.x` accessor.
That is, `{{#example_in Examples/Intro.lean originx}}` and `{{#example_in Examples/Intro.lean originx1}}` both yield
```Lean info
{{#example_out Examples/Intro.lean originx1}}
```

Accessor dot notation is available for any function where Lean is able to determine the type of the first argument.
If `EXPR1` has type `T`, then `EXPR1.f EXPR2` is converted into `T.f EXPR1 EXPR2`.
For instance, `String.append` can be invoked from a string with accessor notation, even though `String` is not a structure with an `append` field.
```Lean
{{#example_in Examples/Intro.lean stringAppendDot}}
```
```Lean info
{{#example_out Examples/Intro.lean stringAppendDot}}
```


# Exercises

 * Define a structure named `RectangularPrism` that contains the height, width, and depth of a rectangular prism, each as a `Float`.
 * Define a function named `volume : RectangularPrism → Float` that computes the volume of a rectangular prism.
 * Define a structure named `Segment` that represents a line segment by its endpoints, and define a function `length : Segment → Float` that computes the length of a line segment. `Segment` should have at most two fields. 
 * Which names are introduced by the declaration of `RectangularPrism`?
 * Which names are introduced by the following declarations of `Hamster` and `Book`? What are their types?

```Lean
{{#example_decl Examples/Intro.lean Hamster}}
```
   
```Lean
{{#example_decl Examples/Intro.lean Book}}
```

