import VersoManual
import FPLean.Examples

open Verso.Genre Manual ExternalLean

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "Structures and Inheritance" =>

In order to understand the full definitions of `Functor`, `Applicative`, and `Monad`, another Lean feature is necessary: structure inheritance.
Structure inheritance allows one structure type to provide the interface of another, along with additional fields.
This can be useful when modeling concepts that have a clear taxonomic relationship.
For example, take a model of mythical creatures.
Some of them are large, and some are small:

```anchor MythicalCreature
structure MythicalCreature where
  large : Bool
deriving Repr
```
Behind the scenes, defining the `MythicalCreature` structure creates an inductive type with a single constructor called `mk`:
```anchor MythicalCreatureMk
#check MythicalCreature.mk
```
```anchorInfo MythicalCreatureMk
MythicalCreature.mk (large : Bool) : MythicalCreature
```
Similarly, a function `MythicalCreature.large` is created that actually extracts the field from the constructor:
```anchor MythicalCreatureLarge
#check MythicalCreature.large
```
```anchorInfo MythicalCreatureLarge
MythicalCreature.large (self : MythicalCreature) : Bool
```

In most old stories, each monster can be defeated in some way.
A description of a monster should include this information, along with whether it is large:

```anchor Monster
structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr
```
The `extends MythicalCreature` in the heading states that every monster is also mythical.
To define a `Monster`, both the fields from `MythicalCreature` and the fields from `Monster` should be provided.
A troll is a large monster that is vulnerable to sunlight:

```anchor troll
def troll : Monster where
  large := true
  vulnerability := "sunlight"
```

Behind the scenes, inheritance is implemented using composition.
The constructor `Monster.mk` takes a `MythicalCreature` as its argument:
```anchor MonsterMk
#check Monster.mk
```
```anchorInfo MonsterMk
Monster.mk (toMythicalCreature : MythicalCreature) (vulnerability : String) : Monster
```
In addition to defining functions to extract the value of each new field, a function {anchorTerm MonsterToCreature}`Monster.toMythicalCreature` is defined with type {anchorTerm MonsterToCreature}`Monster → MythicalCreature`.
This can be used to extract the underlying creature.

Moving up the inheritance hierarchy in Lean is not the same thing as upcasting in object-oriented languages.
An upcast operator causes a value from a derived class to be treated as an instance of the parent class, but the value retains its identity and structure.
In Lean, however, moving up the inheritance hierarchy actually erases the underlying information.
To see this in action, consider the result of evaluating `troll.toMythicalCreature`:
```anchor evalTrollCast
#eval troll.toMythicalCreature
```
```anchorInfo evalTrollCast
{ large := true }
```
Only the fields of `MythicalCreature` remain.


Just like the {kw}`where` syntax, curly-brace notation with field names also works with structure inheritance:

```anchor troll2
def troll : Monster := {large := true, vulnerability := "sunlight"}
```
However, the anonymous angle-bracket notation that delegates to the underlying constructor reveals the internal details:
```anchor wrongTroll1
def troll : Monster := ⟨true, "sunlight"⟩
```
```anchorError wrongTroll1
application type mismatch
  Monster.mk true
argument
  true
has type
  Bool : Type
but is expected to have type
  MythicalCreature : Type
```
An extra set of angle brackets is required, which invokes `MythicalCreature.mk` on `true`:

```anchor troll3
def troll : Monster := ⟨⟨true⟩, "sunlight"⟩
```


Lean's dot notation is capable of taking inheritance into account.
In other words, the existing `MythicalCreature.large` can be used with a `Monster`, and Lean automatically inserts the call to {anchorTerm MonsterToCreature}`Monster.toMythicalCreature` before the call to `MythicalCreature.large`.
However, this only occurs when using dot notation, and applying the field lookup function using normal function call syntax results in a type error:
```anchor trollLargeNoDot
#eval MythicalCreature.large troll
```
```anchorError trollLargeNoDot
application type mismatch
  MythicalCreature.large troll
argument
  troll
has type
  Monster : Type
but is expected to have type
  MythicalCreature : Type
```
Dot notation can also take inheritance into account for user-defined functions.
A small creature is one that is not large:

```anchor small
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
```
Evaluating {anchorTerm smallTroll}`troll.small` yields {anchorTerm smallTroll}`false`, while attempting to evaluate {anchorTerm smallTrollWrong}`MythicalCreature.small troll` results in:
```anchorError smallTrollWrong
application type mismatch
  MythicalCreature.small troll
argument
  troll
has type
  Monster : Type
but is expected to have type
  MythicalCreature : Type
```

# Multiple Inheritance

A helper is a mythical creature that can provide assistance when given the correct payment:

```anchor Helper
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr
```
For example, a _nisse_ is a kind of small elf that's known to help around the house when provided with tasty porridge:

```anchor elf
def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"
```

If domesticated, trolls make excellent helpers.
They are strong enough to plow a whole field in a single night, though they require model goats to keep them satisfied with their lot in life.
A monstrous assistant is a monster that is also a helper:

```anchor MonstrousAssistant
structure MonstrousAssistant extends Monster, Helper where
deriving Repr
```
A value of this structure type must fill in all of the fields from both parent structures:

```anchor domesticatedTroll
def domesticatedTroll : MonstrousAssistant where
  large := true
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"
```

Both of the parent structure types extend `MythicalCreature`.
If multiple inheritance were implemented naïvely, then this could lead to a "diamond problem", where it would be unclear which path to `large` should be taken from a given `MonstrousAssistant`.
Should it take `large` from the contained `Monster` or from the contained `Helper`?
In Lean, the answer is that the first specified path to the grandparent structure is taken, and the additional parent structures' fields are copied rather than having the new structure include both parents directly.

This can be seen by examining the signature of the constructor for `MonstrousAssistant`:
```anchor checkMonstrousAssistantMk
#check MonstrousAssistant.mk
```
```anchorInfo checkMonstrousAssistantMk
MonstrousAssistant.mk (toMonster : Monster) (assistance payment : String) : MonstrousAssistant
```
It takes a `Monster` as an argument, along with the two fields that `Helper` introduces on top of `MythicalCreature`.
Similarly, while `MonstrousAssistant.toMonster` merely extracts the `Monster` from the constructor, `MonstrousAssistant.toHelper` has no `Helper` to extract.
The `#print` command exposes its implementation:
```anchor printMonstrousAssistantToHelper
#print MonstrousAssistant.toHelper
```
```anchorInfo printMonstrousAssistantToHelper
@[reducible] def MonstrousAssistant.toHelper : MonstrousAssistant → Helper :=
fun self => { toMythicalCreature := self.toMythicalCreature, assistance := self.assistance, payment := self.payment }
```
This function constructs a `Helper` from the fields of `MonstrousAssistant`.
The `@[reducible]` attribute has the same effect as writing `abbrev`.

## Default Declarations

When one structure inherits from another, default field definitions can be used to instantiate the parent structure's fields based on the child structure's fields.
If more size specificity is required than whether a creature is large or not, a dedicated datatype describing sizes can be used together with inheritance, yielding a structure in which the `large` field is computed from the contents of the `size` field:

```anchor SizedCreature
inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large
```
This default definition is only a default definition, however.
Unlike property inheritance in a language like C# or Scala, the definitions in the child structure are only used when no specific value for `large` is provided, and nonsensical results can occur:

```anchor nonsenseCreature
def nonsenseCreature : SizedCreature where
  large := false
  size := .large
```
If the child structure should not deviate from the parent structure, there are a few options:

 1. Documenting the relationship, as is done for `BEq` and `Hashable`
 2. Defining a proposition that the fields are related appropriately, and designing the API to require evidence that the proposition is true where it matters
 3. Not using inheritance at all

The second option could look like this:

```anchor sizesMatch
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)
```
Note that a single equality sign is used to indicate the equality _proposition_, while a double equality sign is used to indicate a function that checks equality and returns a `Bool`.
`SizesMatch` is defined as an `abbrev` because it should automatically be unfolded in proofs, so that `simp` can see the equality that should be proven.

A _huldre_ is a medium-sized mythical creature—in fact, they are the same size as humans.
The two sized fields on `huldre` match one another:

```anchor huldresize
def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by
  decide
```


## Type Class Inheritance

Behind the scenes, type classes are structures.
Defining a new type class defines a new structure, and defining an instance creates a value of that structure type.
They are then added to internal tables in Lean that allow it to find the instances upon request.
A consequence of this is that type classes may inherit from other type classes.

Because it uses precisely the same language features, type class inheritance supports all the features of structure inheritance, including multiple inheritance, default implementations of parent types' methods, and automatic collapsing of diamonds.
This is useful in many of the same situations that multiple interface inheritance is useful in languages like Java, C# and Kotlin.
By carefully designing type class inheritance hierarchies, programmers can get the best of both worlds: a fine-grained collection of independently-implementable abstractions, and automatic construction of these specific abstractions from larger, more general abstractions.
