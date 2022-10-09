# Standard Classes

This section presents a variety of operators that can be overloaded using type classes in Lean.
After skimming it to see what's available, it's probably most useful as a reference later on.

## Arithmetic

Most arithmetic operators are available in a heterogeneous form, where the arguments may have different type and an output parameter decides the type of the resulting expression.
For each heterogeneous operator, there is a corresponding homogeneous version that can found by removing the letter `h`, so that `HAdd.hAdd` becomes `Add.add`.
The following arithmetic operators are overloaded:

| Expression | Desugaring | Class Name |
|------------|------------|------------|
| `{{#example_in Examples/Classes.lean plusDesugar}}` | `{{#example_out Examples/Classes.lean plusDesugar}}` | `Add` |
| `{{#example_in Examples/Classes.lean minusDesugar}}` | `{{#example_out Examples/Classes.lean minusDesugar}}` | `Sub` |
| `{{#example_in Examples/Classes.lean timesDesugar}}` | `{{#example_out Examples/Classes.lean timesDesugar}}` | `Mul` |
| `{{#example_in Examples/Classes.lean divDesugar}}` | `{{#example_out Examples/Classes.lean divDesugar}}` | `Div` |
| `{{#example_in Examples/Classes.lean modDesugar}}` | `{{#example_out Examples/Classes.lean modDesugar}}` | `Mod` |
| `{{#example_in Examples/Classes.lean powDesugar}}` | `{{#example_out Examples/Classes.lean powDesugar}}` | `Pow` |
| `{{#example_in Examples/Classes.lean negDesugar}}` | `{{#example_out Examples/Classes.lean negDesugar}}` | `Neg` |


## Bitwise Operators

Lean contains a number of standard bitwise operators that are overloaded using type classes.
There are instances for fixed-width types such as `{{#example_in Examples/Classes.lean UInt8}}`, `{{#example_in Examples/Classes.lean UInt16}}`, `{{#example_in Examples/Classes.lean UInt32}}`, `{{#example_in Examples/Classes.lean UInt64}}`, and `{{#example_in Examples/Classes.lean USize}}`.
The latter is the size of words on the current platform, typically 32 or 64 bits.
The following bitwise operators are overloaded:

| Expression | Desugaring | Class Name |
|------------|------------|------------|
| `{{#example_in Examples/Classes.lean bAndDesugar}}` | `{{#example_out Examples/Classes.lean bAndDesugar}}` | `AndOp` |
| <code class="hljs">x &#x7c;&#x7c;&#x7c; y </code> | `{{#example_out Examples/Classes.lean bOrDesugar}}` | `OrOp` |
| `{{#example_in Examples/Classes.lean bXorDesugar}}` | `{{#example_out Examples/Classes.lean bXorDesugar}}` | `Xor` |
| `{{#example_in Examples/Classes.lean complementDesugar}}` | `{{#example_out Examples/Classes.lean complementDesugar}}` | `Complement` |
| `{{#example_in Examples/Classes.lean shrDesugar}}` | `{{#example_out Examples/Classes.lean shrDesugar}}` | `ShiftRight` |
| `{{#example_in Examples/Classes.lean shlDesugar}}` | `{{#example_out Examples/Classes.lean shlDesugar}}` | `ShiftLeft` |

## Equality and Ordering

Testing equality of two values typically uses the `BEq` class, which is short for "Boolean equality".
Due to Lean's use as a theorem prover, there are really two kinds of equality operators in Lean:
 * _Boolean equality_ is the same kind of equality that is found in other programming languages. It is a function that takes two values and returns a `Bool`. Boolean equality is written with two equals signs, just as in Python and C#. Because Lean is a pure functional language, there's no separate notions of reference vs value equality—pointers cannot be observed directly.
 * _Propositional equality_ is the mathematical statement that two things are equal. Propositional equality is not a function; rather, it is a mathematical statement that admits proof. It is written with a single equals sign. A statement of propositional equality is like a type that classifies evidence of this equality.
 
Both notions of equality are important, and used for different purposes.
Boolean equality is useful in programs, when a decision needs to be made about whether two values are equal.
For instance, `{{#example_in Examples/Classes.lean boolEqTrue}}` evaluates to `{{#example_out Examples/Classes.lean boolEqTrue}}`, and `{{#example_in Examples/Classes.lean boolEqFalse}}` evaluates to `{{#example_out Examples/Classes.lean boolEqFalse}}`.
Some values, such as functions, cannot be checked for equality.
For example, `{{#example_in Examples/Classes.lean functionEq}}` yields the error:
```Lean error
{{#example_out Examples/Classes.lean functionEq}}
```
As this message indicates, `==` is overloaded using a type class.
The expression `{{#example_in Examples/Classes.lean beqDesugar}}` is actually shorthand for `{{#example_out Examples/Classes.lean beqDesugar}}`.

Propositional equality is a mathematical statement rather than an invocation of a program.
Because propositions are like types that describe evidence for some statement, propositional equality has more in common with types like `String` and `Nat → List Int` than it does with Boolean equality.
This means that it can't automatically be checked.
However, the equality of any two expressions can be stated in Lean, so long as they have the same type.
The statement `{{#example_in Examples/Classes.lean functionEqProp}}` is a perfectly reasonable statement.
From the perspective of mathematics, two functions are equal if they map equal inputs to equal outputs, so this statement is even true, though it requires a two-line proof to convince Lean of this fact.

Generally speaking, when using Lean as a programming language, it's easiest to stick to Boolean functions rather than propositions.
However, as the names `true` and `false` for `Bool`'s constructors suggest, this difference is sometimes blurred.
Some propositions are _decidable_, which means that they can be checked just like a Boolean function.
The function that checks whether the proposition is true or false is called a _decision procedure_, and it returns _evidence_ of the truth or falsity of the proposition.
Some examples of decidable propositions include equality and inequality of natural numbers, equality of strings, and "ands" and "ors" of propositions that are themselves decidable.

In Lean, decidable propositions can be used just like Booleans.
For example, `2 < 4` is a proposition:
```Lean
{{#example_in Examples/Classes.lean twoLessFour}}
```
```Lean info
{{#example_out Examples/Classes.lean twoLessFour}}
```
Nonetheless, it is perfectly acceptable to write it as the condition in an `if`.
For instance, `{{#example_in Examples/Classes.lean ifProp}}` has type `Nat` and evaluates to `{{#example_out Examples/Classes.lean ifProp}}`.


Not all propositions are decidable.
If they were, then computers would be able to prove any true proposition just by running the decision procedure.
More specifically, decidable propositions have an instance of the `Decidable` type class which has a method that is the decision procedure.
Trying to use a proposition that isn't decidable as if it were a `Bool` results in a failure to find the `Decidable` instance.
For example, `{{#example_in Examples/Classes.lean funEqDec}}` results in:
```Lean error
{{#example_out Examples/Classes.lean funEqDec}}
```

The following propositions, that are usually decidable, are overloaded with type classes:

| Expression | Desugaring | Class Name |
|------------|------------|------------|
| `{{#example_in Examples/Classes.lean ltDesugar}}` | `{{#example_out Examples/Classes.lean ltDesugar}}` | `LT` |
| `{{#example_in Examples/Classes.lean leDesugar}}` | `{{#example_out Examples/Classes.lean leDesugar}}` | `LE` |
| `{{#example_in Examples/Classes.lean gtDesugar}}` | `{{#example_out Examples/Classes.lean gtDesugar}}` | `LT` |
| `{{#example_in Examples/Classes.lean geDesugar}}` | `{{#example_out Examples/Classes.lean geDesugar}}` | `LE` |
Because defining new propositions hasn't yet been demonstrated, it may be difficult to define new instances of `LT` and `LE`.

Additionally, comparing values using `<`, `==`, and `>` can be inefficient.
Checking first whether one value is less than another, and then whether they are equal, can require two traversals over large data structures.
To solve this problem, Java and C# have standard `compareTo` and `CompareTo` methods (respectively) that can be overridden by a class in order to implement all three operations at the same time.
These methods return a negative integer if the receiver is less than the argument, zero if they are equal, and a positive integer if the receiver is greater than the argument.
Rather than overload the meaning of integers, Lean has a built-in inductive type that describes these three possibilities:
```Lean
{{#example_decl Examples/Classes.lean Ordering}}
```
The `Ord` type class can be overloaded to produce these comparisons.
For `Pos`, an implementation can be:
```Lean
{{#example_decl Examples/Classes.lean OrdPos}}
```
In situations where `compareTo` would be the right approach in Java, use `Ord.compare` in Lean.

## Hashing

Java and C# have `hashCode` and `GetHashCode` methods, respectively, that compute a hash of a value for use in data structures such as hash tables.
The Lean equivalent is a type class called `Hashable`:
```Lean
{{#example_decl Examples/Classes.lean Hashable}}
```
If two values are considered equal according to a `BEq` instance for their type, then they should have the same hashes.
In other words, if `x == y` then `hash x == hash y`.
If `x != y`, then `hash x` won't necessarily differ from `hash y` (after all, there are infinitely more `Nat` values than there are `UInt64` values), but data structures built on hashing will have better performance if unequal values are likely to have unequal hashes.
This is the same expectation as in Java and C#.

The standard library contains a function `{{#example_in Examples/Classes.lean mixHash}}` with type `{{#example_out Examples/Classes.lean mixHash}}` that can be used to combine hashes for different fields for a constructor.
A reasonable hash function for an inductive datatype can be written by assigning a unique number to each constructor, and then mixing that number with the hashes of each field.
For instance, a `Hashable` instance for `Pos` can be written:
```Lean
{{#example_decl Examples/Classes.lean HashablePos}}
```
`Hashable` instances for polymorphic types can use recursive instance search.
For instance, hashing a `NonEmptyList α` is only possible when `α` can be hashed:
```Lean
{{#example_decl Examples/Classes.lean HashableNonEmptyList}}
```

## Deriving Standard Classes

Instance of classes like `BEq` and `Hashable` are often quite tedious to implement by hand.
Lean includes a feature called _instance deriving_ that allows the compiler to automatically construct well-behaved instances of many type classes.
In fact, the `deriving Repr` phrase in the definition of `Point` in the [section on structures](../getting-to-know/structures.md) is an example of instance deriving.

Instances can be derived in two ways:
 1. When defining a structure or inductive type, add `deriving` to the end of the type declaration followed by the names of the classes for which instances should be derived.
 2. Write `deriving instance C1, C2, ... for T` to deriving instances of `C1, C2, ...` for the type `T` after the fact.

`BEq` and `Hashable` instances can be derived for `Pos` and `NonEmptyList` using a very small amount of code:
```Lean
{{#example_decl Examples/Classes.lean BEqHashableDerive}}
```

Instance can be derived for at least the following classes:
 * `Inhabited`
 * `BEq`
 * `Repr`
 * `Hashable`
 * `Ord`
In some cases, however, the derived `Ord` instance may not produce precisely the ordering desired in an application.
When this is the case, it's fine to write an `Ord` instance by hand.
The collection of classes for which instances can be derived can be extended by advanced users of Lean.

Aside from the clear advantages in programmer productivity and code readability, deriving instances also makes code easier to maintain, because the instances are updated as the definitions of types evolve.
Changesets involving updates to datatypes need not also have line after line of formulaic modifications to equality tests and hash computation.

## Appending

Many datatypes have some sort of append operator.
In Lean, appending two values is overloaded with the type class `HAppend`, which is a heterogeneous operation like that used for arithmetic operations:
```Lean
{{#example_decl Examples/Classes.lean HAppend}}
```
The syntax `{{#example_in Examples/Classes.lean desugarHAppend}}` desugars to `{{#example_out Examples/Classes.lean desugarHAppend}}`.
For homogeneous cases, it's enough to implement an instance of `Append`, which follows the usual pattern:
```Lean
{{#example_decl Examples/Classes.lean AppendNEList}}
```

After defining the above instance,
```Lean
{{#example_in Examples/Classes.lean appendSpiders}}
```
has the following output:
```Lean info
{{#example_out Examples/Classes.lean appendSpiders}}
```


## Functors

- Functor


## Exercises

 * Write an instance of `HAppend (NonEmpytList α) (List α) (NonEmptyList α)` and test it.
