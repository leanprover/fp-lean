import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "Structures" =>
%%%
tag := "structures"
%%%

The first step in writing a program is usually to identify the problem domain's concepts, and then find suitable representations for them in code.
Sometimes, a domain concept is a collection of other, simpler, concepts.
In that case, it can be convenient to group these simpler components together into a single “package”, which can then be given a meaningful name.
In Lean, this is done using _structures_, which are analogous to {c}`struct`s in C or Rust and {CSharp}`record`s in C#.

Defining a structure introduces a completely new type to Lean that can't be reduced to any other type.
This is useful because multiple structures might represent different concepts that nonetheless contain the same data.
For instance, a point might be represented using either Cartesian or polar coordinates, each being a pair of floating-point numbers.
Defining separate structures prevents API clients from confusing one for another.

Lean's floating-point number type is called {anchorName zeroFloat}`Float`, and floating-point numbers are written in the usual notation.

```anchorTerm onePointTwo
#check 1.2
```


```anchorInfo onePointTwo
1.2 : Float
```


```anchorTerm negativeLots
#check -454.2123215
```


```anchorInfo negativeLots
-454.2123215 : Float
```


```anchorTerm zeroPointZero
#check 0.0
```


```anchorInfo zeroPointZero
0.0 : Float
```

When floating point numbers are written with the decimal point, Lean will infer the type {anchorName zeroFloat}`Float`. If they are written without it, then a type annotation may be necessary.

```anchorTerm zeroNat
#check 0
```


```anchorInfo zeroNat
0 : Nat
```



```anchorTerm zeroFloat
#check (0 : Float)
```


```anchorInfo zeroFloat
0 : Float
```



A Cartesian point is a structure with two {anchorName zeroFloat}`Float` fields, called {anchorName Point}`x` and {anchorName Point}`y`.
This is declared using the {kw}`structure` keyword.


```anchor Point
structure Point where
  x : Float
  y : Float
```

After this declaration, {anchorName Point}`Point` is a new structure type.
The typical way to create a value of a structure type is to provide values for all of its fields inside of curly braces.
The origin of a Cartesian plane is where {anchorName Point}`x` and {anchorName Point}`y` are both zero:

```anchor origin
def origin : Point := { x := 0.0, y := 0.0 }
```

The result of {anchorTerm originEval}`#eval origin` looks very much like the definition of {anchorName origin}`origin`.

```anchorInfo originEval
{ x := 0.000000, y := 0.000000 }
```


Because structures exist to “bundle up” a collection of data, naming it and treating it as a single unit, it is also important to be able to extract the individual fields of a structure.
This is done using dot notation, as in C, Python, Rust, or JavaScript.

```anchorTerm originx
#eval origin.x
```

```anchorInfo originx
0.000000
```


```anchorTerm originy
#eval origin.y
```

```anchorInfo originy
0.000000
```

:::paragraph
This can be used to define functions that take structures as arguments.
For instance, addition of points is performed by adding the underlying coordinate values.
It should be the case that

```anchorTerm addPointsEx
#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }
```

yields

```anchorInfo addPointsEx
{ x := -6.500000, y := 32.200000 }
```
:::

The function itself takes two {anchorName Point}`Point`s as arguments, called {anchorName addPoints}`p1` and {anchorName addPoints}`p2`.
The resulting point is based on the {anchorName addPoints}`x` and {anchorName addPoints}`y` fields of both {anchorName addPoints}`p1` and {anchorName addPoints}`p2`:

```anchor addPoints
def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }
```


Similarly, the distance between two points, which is the square root of the sum of the squares of the differences in their {anchorName Point}`x` and {anchorName Point}`y` components, can be written:

```anchor distance
def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))
```

For example, the distance between $`(1, 2)` and $`(5, -1)` is $`5`:

```anchorTerm evalDistance
#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }
```

```anchorInfo evalDistance
5.000000
```



Multiple structures may have fields with the same names.
A three-dimensional point datatype may share the fields {anchorName Point3D}`x` and {anchorName Point3D}`y`, and be instantiated with the same field names:

```anchor Point3D
structure Point3D where
  x : Float
  y : Float
  z : Float
```

```anchor origin3D
def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }
```

This means that the structure's expected type must be known in order to use the curly-brace syntax.
If the type is not known, Lean will not be able to instantiate the structure.
For example,

```anchorTerm originNoType
#check { x := 0.0, y := 0.0 }
```

leads to the error

```anchorError originNoType
invalid {...} notation, expected type is not known
```


As usual, the situation can be remedied by providing a type annotation.

```anchorTerm originWithAnnot
#check ({ x := 0.0, y := 0.0 } : Point)
```


```anchorInfo originWithAnnot
{ x := 0.0, y := 0.0 } : Point
```


To make programs more concise, Lean also allows the structure type annotation inside the curly braces.

```anchorTerm originWithAnnot2
#check { x := 0.0, y := 0.0 : Point}
```


```anchorInfo originWithAnnot2
{ x := 0.0, y := 0.0 } : Point
```


# Updating Structures
%%%
tag := "updating-structures"
%%%

Imagine a function {anchorName zeroXBad}`zeroX` that replaces the {anchorName zeroXBad}`x` field of a {anchorName zeroXBad}`Point` with {anchorTerm zeroX}`0`.
In most programming language communities, this sentence would mean that the memory location pointed to by {anchorName Point}`x` was to be overwritten with a new value.
However, Lean is a functional programming language.
In functional programming communities, what is almost always meant by this kind of statement is that a fresh {anchorName Point}`Point` is allocated with the {anchorName Point}`x` field pointing to the new value, and all other fields pointing to the original values from the input.
One way to write {anchorName zeroXBad}`zeroX` is to follow this description literally, filling out the new value for {anchorName Point}`x` and manually transferring {anchorName Point}`y`:

```anchor zeroXBad
def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }
```

This style of programming has drawbacks, however.
First off, if a new field is added to a structure, then every site that updates any field at all must be updated, causing maintenance difficulties.
Secondly, if the structure contains multiple fields with the same type, then there is a real risk of copy-paste coding leading to field contents being duplicated or switched.
Finally, the program becomes long and bureaucratic.

Lean provides a convenient syntax for replacing some fields in a structure while leaving the others alone.
This is done by using the {kw}`with` keyword in a structure initialization.
The source of unchanged fields occurs before the {kw}`with`, and the new fields occur after.
For example, {anchorName zeroX}`zeroX` can be written with only the new {anchorName Point}`x` value:

```anchor zeroX
def zeroX (p : Point) : Point :=
  { p with x := 0 }
```

Remember that this structure update syntax does not modify existing values—it creates new values that share some fields with old values.
Given the point {anchorName fourAndThree}`fourAndThree`:

```anchor fourAndThree
def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }
```

evaluating it, then evaluating an update of it using {anchorName zeroX}`zeroX`, then evaluating it again yields the original value:

```anchorTerm fourAndThreeEval
#eval fourAndThree
```


```anchorInfo fourAndThreeEval
{ x := 4.300000, y := 3.400000 }
```


```anchorTerm zeroXFourAndThreeEval
#eval zeroX fourAndThree
```


```anchorInfo zeroXFourAndThreeEval
{ x := 0.000000, y := 3.400000 }
```


```anchorTerm fourAndThreeEval
#eval fourAndThree
```


```anchorInfo fourAndThreeEval
{ x := 4.300000, y := 3.400000 }
```


One consequence of the fact that structure updates do not modify the original structure is that it becomes easier to reason about cases where the new value is computed from the old one.
All references to the old structure continue to refer to the same field values in all of the new values provided.




# Behind the Scenes
%%%
tag := "behind-the-scenes"
%%%

Every structure has a _constructor_.
Here, the term “constructor” may be a source of confusion.
Unlike constructors in languages such as Java or Python, constructors in Lean are not arbitrary code to be run when a datatype is initialized.
Instead, constructors simply gather the data to be stored in the newly-allocated data structure.
It is not possible to provide a custom constructor that pre-processes data or rejects invalid arguments.
This is really a case of the word “constructor” having different, but related, meanings in the two contexts.


By default, the constructor for a structure named {lit}`S` is named {lit}`S.mk`.
Here, {lit}`S` is a namespace qualifier, and {lit}`mk` is the name of the constructor itself.
Instead of using curly-brace initialization syntax, the constructor can also be applied directly.

```anchorTerm checkPointMk
#check Point.mk 1.5 2.8
```

However, this is not generally considered to be good Lean style, and Lean even returns its feedback using the standard structure initializer syntax.

```anchorInfo checkPointMk
{ x := 1.5, y := 2.8 } : Point
```


Constructors have function types, which means they can be used anywhere that a function is expected.
For instance, {anchorName Pointmk}`Point.mk` is a function that accepts two {anchorName Point}`Float`s (respectively {anchorName Point}`x` and {anchorName Point}`y`) and returns a new {anchorName Point}`Point`.

```anchorTerm Pointmk
#check (Point.mk)
```

```anchorInfo Pointmk
Point.mk : Float → Float → Point
```

To override a structure's constructor name, write it with two colons at the beginning.
For instance, to use {anchorName PointCtorNameName}`Point.point` instead of {anchorName Pointmk}`Point.mk`, write:

```anchor PointCtorName
structure Point where
  point ::
  x : Float
  y : Float
```

In addition to the constructor, an accessor function is defined for each field of a structure.
These have the same name as the field, in the structure's namespace.
For {anchorName Point}`Point`, accessor functions {anchorName Pointx}`Point.x` and {anchorName Pointy}`Point.y` are generated.

```anchorTerm Pointx
#check (Point.x)
```

```anchorInfo Pointx
Point.x : Point → Float
```

```anchorTerm Pointy
#check (Point.y)
```

```anchorInfo Pointy
Point.y : Point → Float
```


In fact, just as the curly-braced structure construction syntax is converted to a call to the structure's constructor behind the scenes, the syntax {anchorName addPoints}`x` in the prior definition of {anchorName addPoints}`addPoints` is converted into a call to the {anchorName addPoints}`x` accessor.
That is, {anchorTerm originx}`#eval origin.x` and {anchorTerm originx1}`#eval Point.x origin` both yield

```anchorInfo originx1
0.000000
```


Accessor dot notation is usable with more than just structure fields.
It can also be used for functions that take any number of arguments.
More generally, accessor notation has the form {lit}`TARGET.f ARG1 ARG2 ...`.
If {lit}`TARGET` has type {lit}`T`, the function named {lit}`T.f` is called.
{lit}`TARGET` becomes its leftmost argument of type {lit}`T`, which is often but not always the first one, and {lit}`ARG1 ARG2 ...` are provided in order as the remaining arguments.
For instance, {anchorName stringAppend}`String.append` can be invoked from a string with accessor notation, even though {anchorName Inline}`String` is not a structure with an {anchorName stringAppendDot}`append` field.

```anchorTerm stringAppendDot
#eval "one string".append " and another"
```

```anchorInfo stringAppendDot
"one string and another"
```

In that example, {lit}`TARGET` represents {anchorTerm stringAppendDot}`"one string"` and {lit}`ARG1` represents {anchorTerm stringAppendDot}`" and another"`.

The function {anchorName modifyBoth}`Point.modifyBoth` (that is, {anchorName modifyBothTest}`modifyBoth` defined in the {lit}`Point` namespace) applies a function to both fields in a {anchorName Point}`Point`:

```anchor modifyBoth
def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }
```

Even though the {anchorName Point}`Point` argument comes after the function argument, it can be used with dot notation as well:

```anchorTerm modifyBothTest
#eval fourAndThree.modifyBoth Float.floor
```

```anchorInfo modifyBothTest
{ x := 4.000000, y := 3.000000 }
```

In this case, {lit}`TARGET` represents {anchorName fourAndThree}`fourAndThree`, while {lit}`ARG1` is {anchorName modifyBothTest}`Float.floor`.
This is because the target of the accessor notation is used as the first argument in which the type matches, not necessarily the first argument.

# Exercises
%%%
tag := "structure-exercises"
%%%

 * Define a structure named {anchorName RectangularPrism}`RectangularPrism` that contains the height, width, and depth of a rectangular prism, each as a {anchorName RectangularPrism}`Float`.
 * Define a function named {anchorTerm RectangularPrism}`volume : RectangularPrism → Float` that computes the volume of a rectangular prism.
 * Define a structure named {anchorName RectangularPrism}`Segment` that represents a line segment by its endpoints, and define a function {lit}`length : Segment → Float` that computes the length of a line segment. {anchorName RectangularPrism}`Segment` should have at most two fields.
 * Which names are introduced by the declaration of {anchorName RectangularPrism}`RectangularPrism`?
 * Which names are introduced by the following declarations of {anchorName Hamster}`Hamster` and {anchorName Book}`Book`? What are their types?

    ```anchor Hamster
    structure Hamster where
      name : String
      fluffy : Bool
    ```

    ```anchor Book
    structure Book where
      makeBook ::
      title : String
      author : String
      price : Float
    ```
