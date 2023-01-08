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
This can be used to extract the underlying creature.

Moving up the inheritance hierarchy in Lean is not the same thing as upcasting in object-oriented languages.
An upcast operator causes a value from a derived class to be treated as an instance of the parent class, but the value retains its identity and structure.
In Lean, however, moving up the inheritance hierarchy actually erases the underlying information.
To see this in action, consider the result of evaluating `troll.toMythicalCreature`:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean evalTrollCast}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean evalTrollCast}}
```
Only the fields of `MythicalCreature` remain.


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

If domesticated, trolls make excellent helpers.
They are strong enough to plow a whole field in a single night, though they require model goats to keep them satisfied with their lot in life.
A monstrous assistant is a monster that is also a helper:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean MonstrousAssistant}}
```
A value of this structure type must fill in all of the fields from both parent structures:
```lean
{{#example_decl Examples/FunctorApplicativeMonad.lean domesticatedTroll}}
```

Both of the parent structure types extend `MythicalCreature`.
If multiple inheritance were implemented naïvely, then this could lead to a "diamond problem", where it would be unclear which path to `large` should be taken from a given `MonstrousAssistant`.
Should it take `large` from the contained `Monster` or from the contained `Helper`?
In Lean, the answer is that the first specified path to the grandparent structure is taken, and the additional parent structures' fields are copied rather than having the new structure include both parents directly.

This can be seen by examining the signature of the constructor for `MonstrousAssistant`:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean checkMonstrousAssistantMk}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean checkMonstrousAssistantMk}}
```
It takes a `Monster` as an argument, along with the two fields that `Helper` introduces on top of `MythicalCreature`.
Similarly, while `MonstrousAssistant.toMonster` merely extracts the `Monster` from the constructor, `MonstrousAssistant.toHelper` has no `Helper` to extract.
The `#print` command exposes its implementation:
```lean
{{#example_in Examples/FunctorApplicativeMonad.lean printMonstrousAssistantToHelper}}
```
```output info
{{#example_out Examples/FunctorApplicativeMonad.lean printMonstrousAssistantToHelper}}
```
This function constructs a `Helper` from the fields of `MonstrousAssistant`.
The `@[reducible]` attribute has the same effect as writing `abbrev`.

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
Note that a single equality sign is used to indicate the equality _proposition_, while a double equality sign is used to indicate a function that checks equality and returns a `Bool`.
`SizesMatch` is defined as an `abbrev` because it should automatically be unfolded in proofs, so that `simp` can see the equality that should be proven.

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

Because it uses precisely the same language features, type class inheritance supports all the features of structure inheritance, including multiple inheritance, default implementations of parent types' methods, and automatic collapsing of diamonds.
This is useful in many of the same situations that multiple interface inheritance is useful in languages like Java, C# and Kotlin.
By carefully designing type class inheritance hierarchies, programmers can get the best of both worlds: a fine-grained collection of independently-implementable abstractions, and automatic construction of these specific abstractions from larger, more general abstractions.
