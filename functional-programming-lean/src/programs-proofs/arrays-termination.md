# Arrays and Termination

To write efficient code, it is important to select appropriate data structures.
Linked lists have their place: in some applications, the ability to share the tails of lists is very important.
However, most use cases for a variable-length sequential collection of data are better served by arrays, which have both less memory overhead and better locality.

Arrays, however, have two drawbacks relative to lists:
 1. Arrays are accessed through indexing, rather than by pattern matching, which imposes [proof obligations](../props-proofs-indexing.md) in order to maintain safety.
 2. A loop that processes an entire array is a tail-recursive function, but it does not have an argument that decreases on each call.
 
Making effective use of arrays requires knowing how to prove to Lean that an array index is in bounds, and how to prove that an array index that approaches the size of the array also causes the program to terminate.
Both of these are expressed using an inequality proposition, rather than propositional equality.

## Inequality

Because different types have different notions of ordering, inequality is governed by two type classes, called `LE` and `LT`.
The table in the section on [standard type classes](../type-classes/standard-classes.md#equality-and-ordering) describes how these classes relate to the syntax:

| Expression | Desugaring | Class Name |
|------------|------------|------------|
| `{{#example_in Examples/Classes.lean ltDesugar}}` | `{{#example_out Examples/Classes.lean ltDesugar}}` | `LT` |
| `{{#example_in Examples/Classes.lean leDesugar}}` | `{{#example_out Examples/Classes.lean leDesugar}}` | `LE` |
| `{{#example_in Examples/Classes.lean gtDesugar}}` | `{{#example_out Examples/Classes.lean gtDesugar}}` | `LT` |
| `{{#example_in Examples/Classes.lean geDesugar}}` | `{{#example_out Examples/Classes.lean geDesugar}}` | `LE` |

In other words, a type may customize the meaning of the `<` and `≤` operators, while `>` and `≥` derive their meanings from `<` and `≤`.
The classes `LT` and `LE` have methods that return propositions rather than `Bool`s:
```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean less}}
```

The instance of `LE` for `Nat` delegates to `Nat.le`:
```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean LENat}}
```

### Inductively-Defined Propositions, Predicates, and Relations

`Nat.le` is an _inductively-defined relation_.
Just as `inductive` can be used to create new datatypes, it can also be used to create new propositions.
When a proposition takes an argument, it is referred to as a _predicate_ that may be true for some, but not all, potential arguments.
Propositions that take multiple arguments are called _relations_.

Each constructor of an inductively defined proposition is a way to prove it.
In other words, the declaration of the proposition describes the different forms of evidence that it is true.
A proposition with no arguments that has a single constructor can be quite easy to prove:
```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean EasyToProve}}
```
The proof consists of using its constructor:
```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean fairlyEasy}}
```
In fact, the proposition `True`, which should always be easy to prove, is defined just like `EasyToProve`:
```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean True}}
```

Inductively-defined propositions that don't take arguments are not nearly as interesting as inductively-defined datatypes.
This is because data is interesting in its own right—the natural number `3` is different from the number `35`, and someone who has ordered 3 pizzas will be upset if 35 arrive at their door 30 minutes later.
The constructors of a proposition describe ways in which the proposition can be true, but once a proposition has been proved, there is no need to know _which_ underlying constructors were used.
This is why most interesting inductively-defined types in the `Prop` universe take arguments.

The inductively-defined predicate `IsThree` states that its argument is three:
```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean IsThree}}
```
The mechanism used here is just like [indexed families such as `HasCol`](../dependent-types/typed-queries.md#column-pointers), except the resulting type is a proposition that can be proved rather than data that can be used.

Using this predicate, it is possible to prove that three is indeed three:
```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean threeIsThree}}
```
Similarly, `IsFive` is a predicate that states that its argument is `5`:
```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean IsFive}}
```

If a number is three, then the result of adding two to it should be five.
This can be expressed as a theorem statement:
```lean
{{#example_in Examples/ProgramsProofs/Arrays.lean threePlusTwoFive0}}
```
The resulting goal has a function type:
```output error
{{#example_out Examples/ProgramsProofs/Arrays.lean threePlusTwoFive0}}
```
Thus, the `intro` tactic can be used to convert the argument into an assumption:
```lean
{{#example_in Examples/ProgramsProofs/Arrays.lean threePlusTwoFive1}}
```
```output error
{{#example_out Examples/ProgramsProofs/Arrays.lean threePlusTwoFive1}}
```
Given the assumption that `n` is three, it should be possible to use the constructor of `IsFive` to complete the proof:
```lean
{{#example_in Examples/ProgramsProofs/Arrays.lean threePlusTwoFive1a}}
```
However, this results in an error:
```output error
{{#example_out Examples/ProgramsProofs/Arrays.lean threePlusTwoFive1a}}
```
This error occurs because `n + 2` is not definitionally equal to `5`.
In an ordinary function definition, dependent pattern matching on the assumption `three` could be used to refine `n` to `3`.
The tactic equivalent of dependent pattern matching is `cases`, which has a syntax similar to that of `induction`:
```lean
{{#example_in Examples/ProgramsProofs/Arrays.lean threePlusTwoFive2}}
```
In the remaining case, `n` has been refined to `3`:
```output error
{{#example_out Examples/ProgramsProofs/Arrays.lean threePlusTwoFive2}}
```
Because `3 + 2` is definitionally equal to `5`, the constructor is now applicable:
```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean threePlusTwoFive3}}
```

The standard false proposition `False` has no constructors, making it impossible to provide direct evidence for.
The only way to provide evidence for `False` is if an assumption is itself impossible, similarly to how `nomatch` can be used to mark code that the type system can see is unreachable.
As described in [the initial Interlude on proofs](../props-proofs-indexing.md#connectives), the negation `Not A` is short for `A → False`.
`Not A` can also be written `¬A`.

It is not the case that four is three:
```lean
{{#example_in Examples/ProgramsProofs/Arrays.lean fourNotThree0}}
```
The initial proof goal contains `Not`:
```output error
{{#example_out Examples/ProgramsProofs/Arrays.lean fourNotThree0}}
```
The fact that it's actually a function type can be exposed using `simp`:
```lean
{{#example_in Examples/ProgramsProofs/Arrays.lean fourNotThree1}}
```
```output error
{{#example_out Examples/ProgramsProofs/Arrays.lean fourNotThree1}}
```
Because the goal is a function type, `intro` can be used to convert the argument into an assumption.
There is no need to keep `simp`, as `intro` can unfold the definition of `Not` itself:
```lean
{{#example_in Examples/ProgramsProofs/Arrays.lean fourNotThree2}}
```
```output error
{{#example_out Examples/ProgramsProofs/Arrays.lean fourNotThree2}}
```
In this proof, the `cases` tactic solves the goal immediately:
```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean fourNotThreeDone}}
```
Just as a pattern match on a `Vect String 2` doesn't need to include a case for `Vect.nil`, a proof by cases over `IsThree 4` doesn't need to include a case for `isThree`.

### Inequality on Natural Numbers

The definition of `Nat.le` has a parameter and an index:

```lean
{{#example_decl Examples/ProgramsProofs/Arrays.lean NatLe}}
```

