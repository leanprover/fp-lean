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



## Hashing


## Appending

 - Add, Mul, etc
 - Hashable
 - Ord, BEq
 - Append
 - Functor
