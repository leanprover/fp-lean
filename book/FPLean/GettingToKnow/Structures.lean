import VersoManual
import FPLean.Examples

open Verso.Genre Manual ExternalLean

open FPLean

example_module Examples.Intro

#doc (Manual) "Structures" =>

The first step in writing a program is usually to identify the problem domain's concepts, and then find suitable representations for them in code.
Sometimes, a domain concept is a collection of other, simpler, concepts.
In that case, it can be convenient to group these simpler components together into a single "package", which can then be given a meaningful name.
In Lean, this is done using _structures_, which are analogous to `struct`s in C or Rust and `record`s in C#.

Defining a structure introduces a completely new type to Lean that can't be reduced to any other type.
This is useful because multiple structures might represent different concepts that nonetheless contain the same data.
For instance, a point might be represented using either Cartesian or polar coordinates, each being a pair of floating-point numbers.
Defining separate structures prevents API clients from confusing one for another.

Lean's floating-point number type is called {term}`Float.name`, and floating-point numbers are written in the usual notation.

{exampleIn onePointTwo}


{exampleInfo onePointTwo}


{exampleIn negativeLots}


{exampleInfo negativeLots}


{exampleIn zeroPointZero}


{exampleInfo zeroPointZero}

When floating point numbers are written with the decimal point, Lean will infer the type {term}`Float.name`. If they are written without it, then a type annotation may be necessary.

{exampleIn zeroNat}


{exampleInfo zeroNat}



{exampleIn zeroFloat}


{exampleInfo zeroFloat}



A Cartesian point is a structure with two {term}`Float.name` fields, called {term}`Point.x` and {term}`Point.y`.
This is declared using the {kw}`structure` keyword.


{exampleDecl Point}


After this declaration, {term}`Point.name` is a new structure type.
The final line, which says {kw}`deriving`﻿` `{term}`Repr.name`, asks Lean to generate code to display values of type {term}`Point.name`.
This code is used by {kw}`#eval` to render the result of evaluation for consumption by programmers, analogous to the `repr` function in Python.
It is also possible to override the compiler's generated display code.

The typical way to create a value of a structure type is to provide values for all of its fields inside of curly braces.
The origin of a Cartesian plane is where {term}`Point.x` and {term}`Point.y` are both zero:

{exampleDecl origin}

The result of {exampleIn}`originEval` looks very much like the definition of {term}`origin.name`.

{exampleInfo originEval}


Because structures exist to “bundle up” a collection of data, naming it and treating it as a single unit, it is also important to be able to extract the individual fields of a structure.
This is done using dot notation, as in C, Python, Rust, or JavaScript.

{exampleIn originx}

{exampleInfo originx}


{exampleIn originy}

{exampleInfo originy}


This can be used to define functions that take structures as arguments.
For instance, addition of points is performed by adding the underlying coordinate values.
It should be the case that {exampleIn}`addPointsEx` yields

{exampleInfo addPointsEx}

The function itself takes two {term}`Point.name`s as arguments, called {term}`addPoints.p1` and {term}`addPoints.p2`.
The resulting point is based on the {term}`Point.x` and {term}`Point.y` fields of both {term}`addPoints.p1` and {term}`addPoints.p2`:

{exampleDecl addPoints}


Similarly, the distance between two points, which is the square root of the sum of the squares of the differences in their {term}`Point.x` and {term}`Point.y` components, can be written:

{exampleDecl distance}

For example, the distance between (1, 2) and (5, -1) is 5:

{exampleIn evalDistance}

{exampleInfo evalDistance}



Multiple structures may have fields with the same names.
A three-dimensional point datatype may share the fields {term}`Point.x` and {term}`Point.y`, and be instantiated with the same field names:

{exampleDecl Point3D}

{exampleDecl origin3D}

This means that the structure's expected type must be known in order to use the curly-brace syntax.
If the type is not known, Lean will not be able to instantiate the structure.
For example,

{exampleIn originNoType}

leads to the error

{exampleError originNoType}


As usual, the situation can be remedied by providing a type annotation.

{exampleIn originWithAnnot}


{exampleInfo originWithAnnot}


To make programs more concise, Lean also allows the structure type annotation inside the curly braces.

{exampleIn originWithAnnot2}


{exampleInfo originWithAnnot2}


# Updating Structures

Imagine a function {term}`zeroX.name` that replaces the {term}`Point.x` field of a {term}`Point.name` with {term}`zeroPointZero.term`.
In most programming language communities, this sentence would mean that the memory location pointed to by {term}`Point.x` was to be overwritten with a new value.
However, Lean is a functional programming language.
In functional programming communities, what is almost always meant by this kind of statement is that a fresh {term}`Point.name` is allocated with the {term}`Point.x` field pointing to the new value, and all other fields pointing to the original values from the input.
One way to write {term}`zeroX.name` is to follow this description literally, filling out the new value for {term}`Point.x` and manually transferring {term}`Point.y`:

{exampleDecl zeroXBad}

This style of programming has drawbacks, however.
First off, if a new field is added to a structure, then every site that updates any field at all must be updated, causing maintenance difficulties.
Secondly, if the structure contains multiple fields with the same type, then there is a real risk of copy-paste coding leading to field contents being duplicated or switched.
Finally, the program becomes long and bureaucratic.

Lean provides a convenient syntax for replacing some fields in a structure while leaving the others alone.
This is done by using the {kw}`with` keyword in a structure initialization.
The source of unchanged fields occurs before the {kw}`with`, and the new fields occur after.
For example, {term}`zeroX.name` can be written with only the new {term}`Point.x` value:

{exampleDecl zeroX}

Remember that this structure update syntax does not modify existing values—it creates new values that share some fields with old values.
Given the point {term}`fourAndThree.name`:

{exampleDecl fourAndThree}

evaluating it, then evaluating an update of it using {term}`zeroX.name`, then evaluating it again yields the original value:

{exampleIn fourAndThreeEval}


{exampleInfo fourAndThreeEval}


{exampleIn zeroXFourAndThreeEval}


{exampleInfo zeroXFourAndThreeEval}


{exampleIn fourAndThreeEval}


{exampleInfo fourAndThreeEval}


One consequence of the fact that structure updates do not modify the original structure is that it becomes easier to reason about cases where the new value is computed from the old one.
All references to the old structure continue to refer to the same field values in all of the new values provided.




# Behind the Scenes

Every structure has a _constructor_.
Here, the term "constructor" may be a source of confusion.
Unlike constructors in languages such as Java or Python, constructors in Lean are not arbitrary code to be run when a datatype is initialized.
Instead, constructors simply gather the data to be stored in the newly-allocated data structure.
It is not possible to provide a custom constructor that pre-processes data or rejects invalid arguments.
This is really a case of the word "constructor" having different, but related, meanings in the two contexts.


By default, the constructor for a structure named `S` is named `S.mk`.
Here, `S` is a namespace qualifier, and `mk` is the name of the constructor itself.
Instead of using curly-brace initialization syntax, the constructor can also be applied directly.

{exampleIn checkPointMk}

However, this is not generally considered to be good Lean style, and Lean even returns its feedback using the standard structure initializer syntax.

{exampleInfo checkPointMk}


Constructors have function types, which means they can be used anywhere that a function is expected.
For instance, {term}`Point.mk` is a function that accepts two {term}`Float.name`s (respectively {term}`Point.x` and {term}`Point.y`) and returns a new {term}`Point.name`.

{exampleIn Pointmk}

{exampleInfo Pointmk}

To override a structure's constructor name, write it with two colons at the beginning.
For instance, to use {term}`Point.point` instead of {term}`Point.mk`, write:

{exampleDecl PointCtorName}


In addition to the constructor, an accessor function is defined for each field of a structure.
These have the same name as the field, in the structure's namespace.
For {term}`Point.name`, accessor functions {term}`Point.x.name` and {term}`Point.y.name` are generated.

{exampleIn Pointx}

{exampleInfo Pointx}

{exampleIn Pointy}

{exampleInfo Pointy}


In fact, just as the curly-braced structure construction syntax is converted to a call to the structure's constructor behind the scenes, the syntax {term}`addPoints.p1.x` in the prior definition of {term}`addPoints.name` is converted into a call to the {term}`Point.x.name` accessor.
That is, {exampleIn}`originx` and {exampleIn}`originx1` both yield

{exampleInfo originx1}


Accessor dot notation is usable with more than just structure fields.
It can also be used for functions that take any number of arguments.
More generally, accessor notation has the form `TARGET.f ARG1 ARG2 ...`.
If `TARGET` has type `T`, the function named `T.f` is called.
`TARGET` becomes its leftmost argument of type `T`, which is often but not always the first one, and `ARG1 ARG2 ...` are provided in order as the remaining arguments.
For instance, {term}`String.append` can be invoked from a string with accessor notation, even though {term}`String.name` is not a structure with an `append` field.

{exampleIn stringAppendDot}

{exampleInfo stringAppendDot}

In that example, `TARGET` represents `"one string"` and `ARG1` represents `" and another"`.

The function {term}`Point.modifyBoth` (that is, {term}`modifyBoth.name` defined in the `Point` namespace) applies a function to both fields in a {term}`Point.name`:

{exampleDecl modifyBoth}

Even though the {term}`Point.name` argument comes after the function argument, it can be used with dot notation as well:

{exampleIn modifyBothTest}

{exampleInfo modifyBothTest}

In this case, `TARGET` represents {term}`fourAndThree.name`, while `ARG1` is {term}`Float.floor`.
This is because the target of the accessor notation is used as the first argument in which the type matches, not necessarily the first argument.

# Exercises

 * Define a structure named `RectangularPrism` that contains the height, width, and depth of a rectangular prism, each as a {term}`Float.name`.
 * Define a function named `volume : RectangularPrism → Float` that computes the volume of a rectangular prism.
 * Define a structure named `Segment` that represents a line segment by its endpoints, and define a function `length : Segment → Float` that computes the length of a line segment. `Segment` should have at most two fields.
 * Which names are introduced by the declaration of `RectangularPrism`?
 * Which names are introduced by the following declarations of {term}`Hamster.name` and {term}`Book.name`? What are their types?


{exampleDecl Hamster}



{exampleDecl Book}
