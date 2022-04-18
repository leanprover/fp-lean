
Outline:

 * `Float`
 * Monormorphic structures and accessor notation
 * Namespaces and accessor notation more generally

```Lean
{{#example_decl Examples/Intro.lean Point}}
```

```Lean
{{#example_decl Examples/Intro.lean origin}}
```

```Lean
{{#example_in Examples/Intro.lean originNoType}}
{{#example_out Examples/Intro.lean originNoType}}
```

```Lean
{{#example_in Examples/Intro.lean originWithAnnot}}
{{#example_out Examples/Intro.lean originWithAnnot}}
```

```Lean
{{#example_in Examples/Intro.lean originWithAnnot2}}
{{#example_out Examples/Intro.lean originWithAnnot2}}
```

```Lean
{{#example_in Examples/Intro.lean Pointmk}}
{{#example_out Examples/Intro.lean Pointmk}}
```

```Lean
{{#example_in Examples/Intro.lean Pointx}}
{{#example_out Examples/Intro.lean Pointx}}
```

```Lean
{{#example_in Examples/Intro.lean Pointy}}
{{#example_out Examples/Intro.lean Pointy}}
```


```Lean
{{#example_in Examples/Intro.lean originx1}}
{{#example_out Examples/Intro.lean originx1}}
```

```Lean
{{#example_in Examples/Intro.lean originx}}
{{#example_out Examples/Intro.lean originx}}
```

```Lean
{{#example_in Examples/Intro.lean stringAppendDot}}
{{#example_out Examples/Intro.lean stringAppendDot}}
```


```Lean
{{#example_decl Examples/Intro.lean distance}}
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

