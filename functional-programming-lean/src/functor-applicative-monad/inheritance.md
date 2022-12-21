# Structures and Inheritance

In order to understand the full definitions of `Functor`, `Applicative`, and `Monad`, another Lean feature is necessary: structure inheritance.
Structure inheritance allows one structure type to provide the interface of another, along with additional fields.
This can be useful when modeling concepts that have a clear taxonomic relationship.
For example, take a model of mythical creatures.
Some of them are large, and some are small:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean MythicalCreature}}
```
Behind the scenes, defining the `MythicalCreature` structure creates an inductive type with a single constructor called `mk`:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean MythicalCreatureMk}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean MythicalCreatureMk}}
```
Similarly, a function `MythicalCreature.large` is created that actually extracts the field from the constructor:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean MythicalCreatureLarge}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean MythicalCreatureLarge}}
```

In most old stories, each monster can be defeated in some way.
A description of a monster should include this information, along with whether it is large:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean Monster}}
```
The `extends MythicalCreature` in the heading states that every monster is also mythical.
To define a `Monster`, both the fields from `MythicalCreature` and the fields from `Monster` should be provided.
A troll is a large monster that is vulnerable to sunlight:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean troll}}
```

Behind the scenes, inheritance is implemented using composition.
The constructor `Monster.mk` takes a `MythicalCreature` as its argument:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean MonsterMk}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean MonsterMk}}
```
In addition to defining functions to extract the value of each new field, a function `{{#example_in Examples/FunctorApplicativeMonad.lean MonsterToCreature}}` is defined with type `{{#example_out Examples/FunctorApplicativeMonad.lean MonsterToCreature}}`.
This can be used to extract the underlying creature. TODO show that this is not upcasting - the additional structure is lost

Just like the `where` syntax, curly-brace notation with field names also works with structure inheritance:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean troll2}}
```
However, the anonymous angle-bracket notation that delegates to the underlying constructor reveals the internal details:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean wrongTroll1}}
```
```output error
{{#example_out Examples/FunctorApplicativeMonad.lean wrongTroll1}}
```
An extra set of angle brackets is required, which invokes `MythicalCreature.mk` on `true`:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean troll3}}
```


Lean's dot notation is capable of taking inheritance into account.
In other words, the existing `MythicalCreature.large` can be used with a `Monster`, and Lean automatically inserts the call to `{{#example_in Examples/FunctorApplicativeMonad.lean MonsterToCreature}}` before the call to `MythicalCreature.large`.
However, this only occurs when using dot notation, and applying the field lookup function using normal function call syntax results in a type error:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean trollLargeNoDot}}
```
```output error
{{#example_out Examples/FunctorApplicativeMonad.lean trollLargeNoDot}}
```
Dot notation can also take inheritance into account for user-defined functions.
A small creature is one that is not large:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean small}}
```
Evaluating `{{#example_in Examples/FunctorApplicativeMonad.lean smallTroll}}` yields `{{#example_out Examples/FunctorApplicativeMonad.lean smallTroll}}`, while attempting to evaluate `{{#example_in Examples/FunctorApplicativeMonad.lean smallTrollWrong}}` results in:
```output error
{{#example_out Examples/FunctorApplicativeMonad.lean smallTrollWrong}}
```

### Multiple Inheritance

A helper is a mythical creature that can provide assistance when given the correct payment:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean Helper}}
```
For example, a _nisse_ is a kind of small elf that's known to help around the house when provided with tasty porridge:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean elf}}
```

TODO example of multiple inheritance and field overlap

### Default Declarations

When one structure inherits from another, default field definitions can be used to instantiate the parent structure's fields based on the child structure's fields.
If more size specificity is required than whether a creature is large or not, a dedicated datatype describing sizes can be used together with inheritance, yielding a structure in which the `large` field is computed from the contents of the `size` field:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean SizedCreature}}
```
This default definition is only a default definition, however.
Unlike property inheritance in a language like C# or Scala, the definitions in the child structure are only used when no specific value for `large` is provided, and nonsensical results can occur:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean nonsenseCreature}}
```
If the child structure should not deviate from the parent structure, there are a few options:

 1. Documenting the relationship, as is done for `BEq` and `Hashable`
 2. Defining a proposition that the fields are related appropriately, and designing the API to require evidence that the proposition is true where it matters
 3. Not using inheritance at all

The second option could look like this:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean sizesMatch}}
```

A _huldre_ is a medium-sized mythical creature—in fact, they are the same size as humans.
The two sized fields on `huldre` match one another:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean huldresize}}
```


### Type Class Inheritance

Behind the scenes, type classes are structures.
Defining a new type class defines a new structure, and defining an instance creates a value of that structure type.
They are then added to internal tables in Lean that allow it to find the instances upon request.
A consequence of this is that type classes may inherit from other type classes.

