# Standard Classes

Some type classes that are used either to overload standard Lean operators, or that occur frequently in Lean code... TODO finish this intro

## Arithmetic

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

## Equality, Ordering, and Hashing

Testing equality of two values uses the `BEq` class, which is short for "Boolean equality".
Because Lean is a theorem prover that allows many mathematical concepts to be encoded, it also contains other notions of equality that are a better match for some kinds of mathematics.
`BEq`, however, is the traditional recursive structural equality test that is found in almost all programming languages.
The expression `{{#example_in Examples/Classes.lean beqDesugar}}` is actually shorthand for `{{#example_out Examples/Classes.lean beqDesugar}}`.



## Appending

 - Add, Mul, etc
 - Hashable
 - Ord, BEq
 - Append
 - Functor
