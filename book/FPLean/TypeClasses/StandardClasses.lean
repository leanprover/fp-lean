import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Standard Classes" =>
%%%
tag := "standard-classes"
%%%


This section presents a variety of operators and functions that can be overloaded using type classes in Lean.
Each operator or function corresponds to a method of a type class.
Unlike C++, infix operators in Lean are defined as abbreviations for named functions; this means that overloading them for new types is not done using the operator itself, but rather using the underlying name (such as {moduleName}`HAdd.hAdd`).

# Arithmetic
%%%
tag := "arithmetic-classes"
%%%

Most arithmetic operators are available in a heterogeneous form, where the arguments may have different type and an output parameter decides the type of the resulting expression.
For each heterogeneous operator, there is a corresponding homogeneous version that can found by removing the letter {lit}`h`, so that {moduleName}`HAdd.hAdd` becomes {moduleName}`Add.add`.
The following arithmetic operators are overloaded:

:::table +header

*
 -  Expression
 -  Desugaring
 -  Class Name
*
 -  {anchorTerm plusDesugar}`x + y`
 -  {anchorTerm plusDesugar}`HAdd.hAdd x y`
 -  {moduleName}`HAdd`
*
 -  {anchorTerm minusDesugar}`x - y`
 -  {anchorTerm minusDesugar}`HSub.hSub x y`
 -  {moduleName}`HSub`
*
 -  {anchorTerm timesDesugar}`x * y`
 -  {anchorTerm timesDesugar}`HMul.hMul x y`
 -  {moduleName}`HMul`
*
 -  {anchorTerm divDesugar}`x / y`
 -  {anchorTerm divDesugar}`HDiv.hDiv x y`
 -  {moduleName}`HDiv`
*
 -  {anchorTerm modDesugar}`x % y`
 -  {anchorTerm modDesugar}`HMod.hMod x y`
 -  {moduleName}`HMod`
*
 -  {anchorTerm powDesugar}`x ^ y`
 -  {anchorTerm powDesugar}`HPow.hPow x y`
 -  {moduleName}`HPow`
*
 -  {anchorTerm negDesugar}`- x`
 -  {anchorTerm negDesugar}`Neg.neg x`
 -  {moduleName}`Neg`


:::

# Bitwise Operators
%%%
tag := "bitwise-classes"
%%%

Lean contains a number of standard bitwise operators that are overloaded using type classes.
There are instances for fixed-width types such as {anchorTerm UInt8}`UInt8`, {anchorTerm UInt16}`UInt16`, {anchorTerm UInt32}`UInt32`, {anchorTerm UInt64}`UInt64`, and {anchorTerm USize}`USize`.
The latter is the size of words on the current platform, typically 32 or 64 bits.
The following bitwise operators are overloaded:

:::table +header
*
 -  Expression
 -  Desugaring
 -  Class Name

*
 -  {anchorTerm bAndDesugar}`x &&& y`
 -  {anchorTerm bAndDesugar}`HAnd.hAnd x y`
 -  {moduleName}`HAnd`
*
 -  {anchorTerm bOrDesugar}`x ||| y`
 -  {anchorTerm bOrDesugar}`HOr.hOr x y`
 -  {moduleName}`HOr`
*
 -  {anchorTerm bXorDesugar}`x ^^^ y`
 -  {anchorTerm bXorDesugar}`HXor.hXor x y`
 -  {moduleName}`HXor`
*
 -  {anchorTerm complementDesugar}`~~~x`
 -  {anchorTerm complementDesugar}`Complement.complement x`
 -  {moduleName}`Complement`
*
 -  {anchorTerm shrDesugar}`x >>> y`
 -  {anchorTerm shrDesugar}`HShiftRight.hShiftRight x y`
 -  {moduleName}`HShiftRight`
*
 -  {anchorTerm shlDesugar}`x <<< y`
 -  {anchorTerm shlDesugar}`HShiftLeft.hShiftLeft x y`
 -  {moduleName}`HShiftLeft`

:::

Because the names {anchorName chapterIntro}`And` and {anchorName chapterIntro}`Or` are already taken as the names of logical connectives, the homogeneous versions of {anchorName chapterIntro}`HAnd` and {anchorName chapterIntro}`HOr` are called {anchorName moreOps}`AndOp` and {anchorName moreOps}`OrOp` rather than {anchorName chapterIntro}`And` and {anchorName chapterIntro}`Or`.

# Equality and Ordering
%%%
tag := "equality-and-ordering"
%%%

Testing equality of two values typically uses the {moduleName}`BEq` class, which is short for “Boolean equality”.
Due to Lean's use as a theorem prover, there are really two kinds of equality operators in Lean:
 * {deftech}_Boolean equality_ is the same kind of equality that is found in other programming languages. It is a function that takes two values and returns a {anchorName CoeBoolProp}`Bool`. Boolean equality is written with two equals signs, just as in Python and C#. Because Lean is a pure functional language, there's no separate notions of reference vs value equality—pointers cannot be observed directly.
 * {deftech}_Propositional equality_ is the mathematical statement that two things are equal. Propositional equality is not a function; rather, it is a mathematical statement that admits proof. It is written with a single equals sign. A statement of propositional equality is like a type that classifies evidence of this equality.

Both notions of equality are important, and used for different purposes.
Boolean equality is useful in programs, when a decision needs to be made about whether two values are equal.
For example, {anchorTerm boolEqTrue}`"Octopus" ==  "Cuttlefish"` evaluates to {anchorTerm boolEqTrue}`false`, and {anchorTerm boolEqFalse}`"Octopodes" ==  "Octo".append "podes"` evaluates to {anchorTerm boolEqFalse}`true`.
Some values, such as functions, cannot be checked for equality.
For example, {anchorTerm functionEq}`(fun (x : Nat) => 1 + x) == (Nat.succ ·)` yields the error:
```anchorError functionEq
failed to synthesize
  BEq (Nat → Nat)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
As this message indicates, {lit}`==` is overloaded using a type class.
The expression {anchorTerm beqDesugar}`x == y` is actually shorthand for {anchorTerm beqDesugar}`BEq.beq x y`.

Propositional equality is a mathematical statement rather than an invocation of a program.
Because propositions are like types that describe evidence for some statement, propositional equality has more in common with types like {anchorName readFile}`String` and {anchorTerm moreOps}`Nat → List Int` than it does with Boolean equality.
This means that it can't automatically be checked.
However, the equality of any two expressions can be stated in Lean, so long as they have the same type.
The statement {anchorTerm functionEqProp}`(fun (x : Nat) => 1 + x) = (Nat.succ ·)` is a perfectly reasonable statement.
From the perspective of mathematics, two functions are equal if they map equal inputs to equal outputs, so this statement is even true, though it requires a one-line proof to convince Lean of this fact.

Generally speaking, when using Lean as a programming language, it's easiest to stick to Boolean functions rather than propositions.
However, as the names {moduleName}`true` and {moduleName}`false` for {moduleName}`Bool`'s constructors suggest, this difference is sometimes blurred.
Some propositions are _decidable_, which means that they can be checked just like a Boolean function.
The function that checks whether the proposition is true or false is called a _decision procedure_, and it returns _evidence_ of the truth or falsity of the proposition.
Some examples of decidable propositions include equality and inequality of natural numbers, equality of strings, and “ands” and “ors” of propositions that are themselves decidable.

:::paragraph
In Lean, {kw}`if` works with decidable propositions.
For example, {anchorTerm twoLessFour}`2 < 4` is a proposition:
```anchor twoLessFour
#check 2 < 4
```
```anchorInfo twoLessFour
2 < 4 : Prop
```
Nonetheless, it is perfectly acceptable to write it as the condition in an {kw}`if`.
For example, {anchorTerm ifProp}`if 2 < 4 then 1 else 2` has type {moduleName}`Nat` and evaluates to {anchorTerm ifProp}`1`.
:::

Not all propositions are decidable.
If they were, then computers would be able to prove any true proposition just by running the decision procedure, and mathematicians would be out of a job.
More specifically, decidable propositions have an instance of the {anchorName DecLTLEPos}`Decidable` type class, which contains the decision procedure.
Trying to use a proposition that isn't decidable as if it were a {anchorName CoeBoolProp}`Bool` results in a failure to find the {anchorName DecLTLEPos}`Decidable` instance.
For example, {anchorTerm funEqDec}`if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no"` results in:
```anchorError funEqDec
failed to synthesize
  Decidable ((fun x => 1 + x) = fun x => x.succ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

The following propositions, that are usually decidable, are overloaded with type classes:

:::table +header
*
 -  Expression
 -  Desugaring
 -  Class Name
*
 -  {anchorTerm ltDesugar}`x < y`
 -  {anchorTerm ltDesugar}`LT.lt x y`
 -  {moduleName}`LT`
*
 -  {anchorTerm leDesugar}`x ≤ y`
 -  {anchorTerm leDesugar}`LE.le x y`
 -  {moduleName}`LE`
*
 -  {anchorTerm gtDesugar}`x > y`
 -  {anchorTerm gtDesugar}`LT.lt y x`
 -  {moduleName}`LT`
*
 -  {anchorTerm geDesugar}`x ≥ y`
 -  {anchorTerm geDesugar}`LE.le y x`
 -  {moduleName}`LE`
:::

Because defining new propositions hasn't yet been demonstrated, it may be difficult to define completely new instances of {moduleName}`LT` and {moduleName}`LE`.
However, they can be defined in terms of existing instances.
{moduleName}`LT` and {moduleName}`LE` instances for {anchorName LTPos}`Pos` can use the existing instances for {moduleName}`Nat`:

```anchor LTPos
instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat
```

```anchor LEPos
instance : LE Pos where
  le x y := LE.le x.toNat y.toNat
```
These propositions are not decidable by default because Lean doesn't unfold the definitions of propositions while synthesizing an instance.
This can be bridged using the {anchorName DecLTLEPos}`inferInstanceAs` operator, which finds an instance for a given class if it exists:

```anchor DecLTLEPos
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))

instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat ≤ y.toNat))
```
The type checker confirms that the definitions of the propositions match.
Confusing them results in an error:
```anchor LTLEMismatch
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))
```
```anchorError LTLEMismatch
Type mismatch
  inferInstanceAs (Decidable (x.toNat < y.toNat))
has type
  Decidable (x.toNat < y.toNat)
but is expected to have type
  Decidable (x ≤ y)
```

:::paragraph
Comparing values using {lit}`<`, {lit}`==`, and {lit}`>` can be inefficient.
Checking first whether one value is less than another, and then whether they are equal, can require two traversals over large data structures.
To solve this problem, Java and C# have standard {java}`compareTo` and {CSharp}`CompareTo` methods (respectively) that can be overridden by a class in order to implement all three operations at the same time.
These methods return a negative integer if the receiver is less than the argument, zero if they are equal, and a positive integer if the receiver is greater than the argument.
Rather than overloading the meaning of integers, Lean has a built-in inductive type that describes these three possibilities:
```anchor Ordering
inductive Ordering where
  | lt
  | eq
  | gt
```
The {anchorName OrdPos}`Ord` type class can be overloaded to produce these comparisons.
For {anchorName OrdPos}`Pos`, an implementation can be:
```anchor OrdPos
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp
```
In situations where {java}`compareTo` would be the right approach in Java, use {moduleName}`Ord.compare` in Lean.
:::

# Hashing
%%%
tag := "hashing"
%%%

Java and C# have {java}`hashCode` and {CSharp}`GetHashCode` methods, respectively, that compute a hash of a value for use in data structures such as hash tables.
The Lean equivalent is a type class called {anchorName Hashable}`Hashable`:

```anchor Hashable
class Hashable (α : Type) where
  hash : α → UInt64
```
If two values are considered equal according to a {moduleName}`BEq` instance for their type, then they should have the same hashes.
In other words, if {anchorTerm HashableSpec}`x == y` then {anchorTerm HashableSpec}`hash x == hash y`.
If {anchorTerm HashableSpec}`x ≠ y`, then {anchorTerm HashableSpec}`hash x` won't necessarily differ from {anchorTerm HashableSpec}`hash y` (after all, there are infinitely more {moduleName}`Nat` values than there are {moduleName}`UInt64` values), but data structures built on hashing will have better performance if unequal values are likely to have unequal hashes.
This is the same expectation as in Java and C#.

The standard library contains a function {anchorTerm mixHash}`mixHash` with type {anchorTerm mixHash}`UInt64 → UInt64 → UInt64` that can be used to combine hashes for different fields for a constructor.
A reasonable hash function for an inductive datatype can be written by assigning a unique number to each constructor, and then mixing that number with the hashes of each field.
For example, a {anchorName HashablePos}`Hashable` instance for {anchorName HashablePos}`Pos` can be written:

```anchor HashablePos
def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos
```

:::paragraph
{anchorTerm HashableNonEmptyList}`Hashable` instances for polymorphic types can use recursive instance search.
Hashing a {anchorTerm HashableNonEmptyList}`NonEmptyList α` is only possible when {anchorName HashableNonEmptyList}`α` can be hashed:
```anchor HashableNonEmptyList
instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)
```
:::
:::paragraph
Binary trees use both recursion and recursive instance search in the implementations of {anchorName TreeHash}`BEq` and {anchorName TreeHash}`Hashable`:

```anchor TreeHash
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1
      (mixHash (hashBinTree left)
        (mixHash (hash x)
          (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree
```
:::

# Deriving Standard Classes
%%%
tag := "deriving-standard-classes"
%%%

Instance of classes like {moduleName}`BEq` and {moduleName}`Hashable` are often quite tedious to implement by hand.
Lean includes a feature called _instance deriving_ that allows the compiler to automatically construct well-behaved instances of many type classes.
In fact, the {anchorTerm Firewood (module := Examples.Intro)}`deriving Repr` phrase in the definition of {anchorName Firewood (module:=Examples.Intro)}`Firewood` in the {ref "polymorphism"}[first section on polymorphism] is an example of instance deriving.

Instances can be derived in two ways.
The first can be used when defining a structure or inductive type.
In this case, add {kw}`deriving` to the end of the type declaration followed by the names of the classes for which instances should be derived.
For a type that is already defined, a standalone {kw}`deriving` command can be used.
Write {kw}`deriving instance`{lit}` C1, C2, ... `{kw}`for`{lit}` T` to derive instances of {lit}`C1, C2, ...` for the type {lit}`T` after the fact.

{moduleName}`BEq` and {moduleName}`Hashable` instances can be derived for {anchorName BEqHashableDerive}`Pos` and {anchorName BEqHashableDerive}`NonEmptyList` using a very small amount of code:

```anchor BEqHashableDerive
deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList
```

Instances can be derived for at least the following classes:

 * {moduleName}`Inhabited`
 * {moduleName}`BEq`
 * {moduleName}`Repr`
 * {moduleName}`Hashable`
 * {moduleName}`Ord`

In some cases, however, the derived {moduleName}`Ord` instance may not produce precisely the ordering desired in an application.
When this is the case, it's fine to write an {moduleName}`Ord` instance by hand.
The collection of classes for which instances can be derived can be extended by advanced users of Lean.

Aside from the clear advantages in programmer productivity and code readability, deriving instances also makes code easier to maintain, because the instances are updated as the definitions of types evolve.
When reviewing changes to code, modifications that involve updates to datatypes are much easier to read without line after line of formulaic modifications to equality tests and hash computation.

# Appending
%%%
tag := "append-class"
%%%

Many datatypes have some sort of append operator.
In Lean, appending two values is overloaded with the type class {anchorName HAppend}`HAppend`, which is a heterogeneous operation like that used for arithmetic operations:

```anchor HAppend
class HAppend (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ
```
The syntax {anchorTerm desugarHAppend}`xs ++ ys` desugars to {anchorTerm desugarHAppend}`HAppend.hAppend xs ys`.
For homogeneous cases, it's enough to implement an instance of {moduleName}`Append`, which follows the usual pattern:

```anchor AppendNEList
instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
```

After defining the above instance,
```anchor appendSpiders
#eval idahoSpiders ++ idahoSpiders
```
has the following output:
```anchorInfo appendSpiders
{ head := "Banded Garden Spider",
  tail := ["Long-legged Sac Spider",
           "Wolf Spider",
           "Hobo Spider",
           "Cat-faced Spider",
           "Banded Garden Spider",
           "Long-legged Sac Spider",
           "Wolf Spider",
           "Hobo Spider",
           "Cat-faced Spider"] }
```

Similarly, a definition of {moduleName}`HAppend` allows non-empty lists to be appended to ordinary lists:

```anchor AppendNEListList
instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }
```
With this instance available,
```anchor appendSpidersList
#eval idahoSpiders ++ ["Trapdoor Spider"]
```
results in
```anchorInfo appendSpidersList
{ head := "Banded Garden Spider",
  tail := ["Long-legged Sac Spider", "Wolf Spider", "Hobo Spider", "Cat-faced Spider", "Trapdoor Spider"] }
```

# Functors
%%%
tag := "Functor"
%%%

A polymorphic type is a {deftech}_functor_ if it has an overload for a function named {anchorName FunctorDef}`map` that transforms every element contained in it by a function.
While most languages use this terminology, C#'s equivalent of {anchorName FunctorDef}`map` is called {CSharp}`System.Linq.Enumerable.Select`.
For example, mapping a function over a list constructs a new list in which each entry from the starting list has been replaced by the result of the function on that entry.
Mapping a function {anchorName optionFMeta}`f` over an {anchorName optionFMeta}`Option` leaves {anchorName optionFMeta}`none` untouched, and replaces {anchorTerm optionFMeta}`some x` with {anchorTerm optionFMeta}`some (f x)`.

Here are some examples of functors and how their {anchorName FunctorDef}`Functor` instances overload {anchorName FunctorDef}`map`:
 * {anchorTerm mapList}`Functor.map (· + 5) [1, 2, 3]` evaluates to {anchorTerm mapList}`[6, 7, 8]`
 * {anchorTerm mapOption}`Functor.map toString (some (List.cons 5 List.nil))` evaluates to {anchorTerm mapOption}`some "[5]"`
 * {anchorTerm mapListList}`Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]` evaluates to {anchorTerm mapListList}`[[3, 2, 1], [6, 5, 4]]`

Because {anchorName mapList}`Functor.map` is a bit of a long name for this common operation, Lean also provides an infix operator for mapping a function, namely {lit}`<$>`.
The prior examples can be rewritten as follows:
 * {anchorTerm mapInfixList}`(· + 5) <$> [1, 2, 3]` evaluates to {anchorTerm mapInfixList}`[6, 7, 8]`
 * {anchorTerm mapInfixOption}`toString <$> (some (List.cons 5 List.nil))` evaluates to {anchorTerm mapInfixOption}`some "[5]"`
 * {anchorTerm mapInfixListList}`List.reverse <$> [[1, 2, 3], [4, 5, 6]]` evaluates to {anchorTerm mapInfixListList}`[[3, 2, 1], [6, 5, 4]]`

An instance of {anchorTerm FunctorNonEmptyList}`Functor` for {anchorTerm FunctorNonEmptyList}`NonEmptyList` requires specifying the {anchorName FunctorNonEmptyList}`map` function.

```anchor FunctorNonEmptyList
instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }
```
Here, {anchorTerm FunctorNonEmptyList}`map` uses the {anchorTerm FunctorNonEmptyList}`Functor` instance for {moduleName}`List` to map the function over the tail.
This instance is defined for {anchorTerm FunctorNonEmptyList}`NonEmptyList` rather than for {anchorTerm FunctorNonEmptyListA}`NonEmptyList α` because the argument type {anchorTerm FunctorNonEmptyListA}`α` plays no role in resolving the type class.
A {anchorTerm FunctorNonEmptyList}`NonEmptyList` can have a function mapped over it _no matter what the type of entries is_.
If {anchorTerm FunctorNonEmptyListA}`α` were a parameter to the class, then it would be possible to make versions of {anchorTerm FunctorNonEmptyList}`Functor` that only worked for {anchorTerm FunctorNonEmptyListA}`NonEmptyList Nat`, but part of being a functor is that {anchorName FunctorNonEmptyList}`map` works for any entry type.

:::paragraph
Here is an instance of {anchorTerm FunctorPPoint}`Functor` for {anchorTerm FunctorPPoint}`PPoint`:

```anchor FunctorPPoint
instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }
```
In this case, {anchorName FunctorPPoint}`f` has been applied to both {anchorName FunctorPPoint}`x` and {anchorName FunctorPPoint}`y`.
:::

Even when the type contained in a functor is itself a functor, mapping a function only goes down one layer.
That is, when using  {anchorName FunctorPPoint}`map` on a {anchorTerm NEPP}`NonEmptyList (PPoint Nat)`, the function being mapped should take {anchorTerm NEPP}`PPoint Nat` as its argument rather than {moduleName}`Nat`.

The definition of the {anchorName FunctorLaws}`Functor` class uses one more language feature that has not yet been discussed: default method definitions.
Normally, a class will specify some minimal set of overloadable operations that make sense together, and then use polymorphic functions with instance implicit arguments that build on the overloaded operations to provide a larger library of features.
For example, the function {anchorName concat}`concat` can concatenate any non-empty list whose entries are appendable:

```anchor concat
def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail
```
However, for some classes, there are operations that can be more efficiently implemented with knowledge of the internals of a datatype.

In these cases, a default method definition can be provided.
A default method definition provides a default implementation of a method in terms of the other methods.
However, instance implementors may choose to override this default with something more efficient.
Default method definitions contain {lit}`:=` in a {kw}`class` definition.

In the case of {anchorName FunctorDef}`Functor`, some types have a more efficient way of implementing {anchorName FunctorDef}`map` when the function being mapped ignores its argument.
Functions that ignore their arguments are called _constant functions_ because they always return the same value.
Here is the definition of {anchorName FunctorDef}`Functor`, in which {anchorName FunctorDef}`mapConst` has a default implementation:

```anchor FunctorDef
class Functor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

  mapConst {α β : Type} (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll
```

Just as a {anchorName HashableSpec}`Hashable` instance that doesn't respect {moduleName}`BEq` is buggy, a {moduleName}`Functor` instance that moves around the data as it maps the function is also buggy.
For example, a buggy {moduleName}`Functor` instance for {moduleName}`List` might throw away its argument and always return the empty list, or it might reverse the list.
A bad {moduleName}`Functor` instance for {moduleName}`PPoint` might place {anchorTerm FunctorPPointBad}`f x` in both the {anchorName FunctorPPointBad}`x` and the {anchorName FunctorPPointBad}`y` fields, or swap them.
Specifically, {anchorName FunctorDef}`Functor` instances should follow two rules:
 1. Mapping the identity function should result in the original argument.
 2. Mapping two composed functions should have the same effect as composing their mapping.

More formally, the first rule says that {anchorTerm FunctorLaws}`id <$> x` equals {anchorTerm FunctorLaws}`x`.
The second rule says that {anchorTerm FunctorLaws}`map (fun y => f (g y)) x` equals {anchorTerm FunctorLaws}`map f (map g x)`.
The composition {anchorTerm compDef}`f ∘ g` can also be written {anchorTerm compDef}`fun y => f (g y)`.
These rules prevent implementations of {anchorName FunctorDef}`map` that move the data around or delete some of it.

# Messages You May Meet
%%%
tag := "standard-classes-messages"
%%%

Lean is not able to derive instances for all classes.
For example, the code
```anchor derivingNotFound
deriving instance ToString for NonEmptyList
```
results in the following error:
```anchorError derivingNotFound
No deriving handlers have been implemented for class `ToString`
```
Invoking {anchorTerm derivingNotFound}`deriving instance` causes Lean to consult an internal table of code generators for type class instances.
If the code generator is found, then it is invoked on the provided type to create the instance.
This message, however, means that no code generator was found for {anchorName derivingNotFound}`ToString`.

# Exercises
%%%
tag := "standard-classes-exercises"
%%%

 * Write an instance of {anchorTerm moreOps}`HAppend (List α) (NonEmptyList α) (NonEmptyList α)` and test it.
 * Implement a {anchorTerm FunctorLaws}`Functor` instance for the binary tree datatype.
