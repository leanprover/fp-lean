# Pitfalls of Programming with Dependent Types

The flexibility of dependent types allows more useful programs to be accepted by a type checker, because the language of types is expressive enough to describe variations that less-expressive type systems cannot.
At the same time, the ability of dependent types to express very fine-grained specifications allows more buggy programs to be rejected by a type checker.
This power comes at a cost.

The close coupling between the internals of type-returning functions such as `Row` and the types that they produce is an instance of a bigger difficulty: the distinction between the interface and the implementation of functions begins to break down when functions are used in types.
Normally, all refactorings are valid as long as they don't change the type signature or input-output behavior of a function.
Functions can be rewritten to use more efficient algorithms and data structures, bugs can be fixed, and code clarity can be improved without breaking client code.
When the function is used in a type, however, the internals of the function's implementation become part of the type, and thus part of _interface_ to another program.

As an example, take the following two implementations of addition on `Nat`.
`Nat.plusL` is recursive on its first argument:
```lean
{{#example_decl Examples/DependentTypes/Pitfalls.lean plusL}}
```
`Nat.plusR`, on the other hand, is recursive on its second argument:
```lean
{{#example_decl Examples/DependentTypes/Pitfalls.lean plusR}}
```
Both implementations of addition are faithful to the underlying mathematical concept, and they thus return the same result when given the same arguments.

However, these two implementations present quite different interfaces when they are used in types.
As an example, take a function that appends two `Vect`s.
This function should return a `Vect` whose length is the sum of the length of the arguments.
Because `Vect` is essentially a `List` with a more informative type, it makes sense to write the function just as one would for `List.append`, with pattern matching and recursion on the first argument.
Starting with a type signature and initial pattern match pointing at placeholders yields two messages:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean appendL1}}
```
The first message, in the `nil` case, states that the placeholder should be replaced by a `Vect` with length `plusL 0 k`:
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendL1}}
```
The second message, in the `cons` case, states that the placeholder should be replaced by a `Vect` with length `plusL (n✝ + 1) k`:
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendL2}}
```
The symbol after `n`, called a _dagger_, is used to indicate names that Lean has internally invented.
Behind the scenes, pattern matching on the first `Vect` implicitly caused the value of the first `Nat` to be refined as well, because the index on the constructor `cons` is `n + 1`, with the tail of the `Vect` having length `n`.
Here, `n✝` represents the `Nat` that is one less than the argument `n`.

## Definitional Equality

In the definition of `plusL`, there is a pattern case `0, k => k`.
This applies in the length used in the first placeholder, so another way to write the underscore's type `Vect α (Nat.plusL 0 k)` is `Vect α k`.
Similarly, `plusL` contains a pattern case `n + 1, k => plusN n k + 1`.
This means that the type of the second underscore can be equivalently written `Vect α (plusL n✝ k + 1)`.

To expose what is going on behind the scenes, the first step is to write the `Nat` arguments explicitly, which also results in daggerless error messages because the names are now written explicitly in the program:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean appendL3}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendL3}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendL4}}
```
Annotating the underscores with the simplified versions of the types does not introduce a type error, which means that the types as written in the program are equivalent to the ones that Lean found on its own:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean appendL5}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendL5}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendL6}}
```

The first case demands a `Vect α k`, and `ys` has that type.
This is parallel to the way that appending the empty list to any other list returns that other list.
Refining the definition with `ys` instead of the first underscore yields a program with only one remaining underscore to be filled out:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean appendL7}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendL7}}
```

Something very important has happened here.
In a context where Lean expected a `Vect α (Nat.plusL 0 k)`, it received a `Vect α k`.
However, `Nat.plusL` is not an `abbrev`, so it may seem like it shouldn't be running during type checking.
Something else is happening.

The key to understanding what's going on is that Lean doesn't just expand `abbrev`s while type checking.
It can also perform computation while checking whether two types are equivalent to one another, such that any expression of one type can be used in a context that expects the other type.
This property is called _definitional equality_, and it is subtle.

Certainly, two types that are written identically are considered to be definitionally equal—`Nat` and `Nat` or `List String` and `List String` should be considered equal.
Any two concrete types built from different datatypes are not equal, so `List Nat` is not equal to `Int`.
Additionally, types that differ only by renaming internal names are equal, so `(n : Nat) → Vect String n` is the same as `(k : Nat) → Vect String k`.
Because types can contain ordinary data, definitional equality must also describe when data are equal.
Uses of the same constructors are equal, so `0` equals `0` and `[5, 3, 1]` equals `[5, 3, 1]`.

Types contain more than just function arrows, datatypes, and constructors, however.
They also contain _variables_ and _functions_.
Definitional equality of variables is relatively simple: each variable is equal only to itself, so `(n k : Nat) → Vect Int n` is not definitionally equal to `(n k : Nat) → Vect Int k`.
Functions, on the other hand, are more complicated.
While mathematics considers two functions to be equal if they have identical input-output behavior, there is no efficient algorithm to check that, and the whole point of definitional equality is for Lean to check whether two types are interchangeable.
Instead, Lean considers functions to be definitionally equal either when they are both `fun`-expressions with definitionally equal bodies.
In other words, two functions must use _the same algorithm_ that calls _the same helpers_ to be considered definitionally equal.
This is not typically very helpful, so definitional equality of functions is mostly used when the exact same defined function occurs in two types.

When functions are _called_ in a type, checking definitional equality may involve reducing the function call.
The type `Vect String (1 + 4)` is definitionally equal to the type `Vect String (3 + 2)` because `1 + 4` is definitionally equal to `3 + 2`.
To check their equality, both are reduced to `5`, and then the constructor rule can be used five times.
Definitional equality of functions applied to data can be checked first by seeing if they're already the same—there's no need to reduce `["a", "b"] ++ ["c"]` to check that it's equal to `["a", "b"] ++ ["c"]`, after all.
If not, the function is called and replaced with its value, and the value can then be checked.

Not all function arguments are concrete data.
For example, types may contain `Nat`s that are not built from the `zero` and `succ` constructors.
In the type `(n : Nat) → Vect String n`, the variable `n` is a `Nat`, but it is impossible to know _which_ `Nat` it is before the function is called.
Indeed, the function may be called first with `0`, and then later with `17`, and then again with `33`.
As seen in the definition of `appendL`, variables with type `Nat` may also be passed to functions such as `plusL`.
Indeed, the type `(n : Nat) → Vect String n` is definitionally equal to the type `(n : Nat) → Vect String (Nat.plusL 0 n)`.

The reason that `n` and `Nat.plusL 0 n` are definitionally equal is that `plusL`'s pattern match examines its _first_ argument.
This is problematic: `(n : Nat) → Vect String n` is _not_ definitionally equal to `(n : Nat) → Vect String (Nat.plusL n 0)`, even though zero should be both a left and a right identity of addition.
This happens because pattern matching gets stuck when it encounters variables.
Until the actual value of `n` becomes known, there is no way to know which case of `Nat.plusL n 0` should be selected.

The same issue appears with the `Row` function in the query example.
The type `Row (c :: cs)` does not reduce to any datatype because the definition of `Row` has separate cases for singleton lists and lists with at least two entries.
In other words, it gets stuck when trying to match the variable `cs` against concrete `List` constructors.
This is why almost every function that takes apart or constructors a `Row` needs to match the same three cases as `Row` itself: getting it unstuck reveals concrete types that can be used for either pattern matching or constructors.

The missing case in `appendL` requires a `Vect α (Nat.plusL n k + 1)`.
The `+ 1` in the index suggests that the next step is to use `Vect.cons`:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean appendL8}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendL8}}
```
A recursive call to `appendL` can construct a `Vect` with the desired length:
```lean
{{#example_decl Examples/DependentTypes/Pitfalls.lean appendL9}}
```
Now that the program is finished, removing the explicit matching on `n` and `k` makes it easier to read and easier to call the function:
```lean
{{#example_decl Examples/DependentTypes/Pitfalls.lean appendL}}
```

Comparing types using definitional equality means that everything involved in definitional equality, including the internals of function definitions, becomes part of the _interface_ of programs that use dependent types and indexed families.
Exposing the internals of a function in a type means that refactoring the exposed program may cause programs that use it to no longer type check.
In particular, the fact that `plusL` is used in the type of `appendL` means that the definition of `plusL` cannot be replaced by the otherwise-equivalent `plusR`.

## Getting Stuck on Addition

What happens if append is defined with `plusR` instead?
Beginning in the same way, with explicit lengths and placeholder underscores in each case, reveals the following useful error messages:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean appendR1}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendR1}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendR2}}
```
However, attempting to place a `Vect α k` type annotation around the first placeholder results in an type mismatch error:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean appendR3}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendR3}}
```
This error is pointing out that `plusR 0 k` and `k` are _not_ definitionally equal.

This is because `plusR` has the following definition:
```lean
{{#example_decl Examples/DependentTypes/Pitfalls.lean plusR}}
```
Its pattern matching occurs on the _second_ argument, not the first argument, which means that the presence of the variable `k` in that position prevents it from reducing.
`Nat.add` in Lean's standard library is equivalent to `plusR`, not `plusL`, so attempting to use it in this definition results in precisely the same difficulties:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean appendR4}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendR4}}
```

Addition is getting _stuck_ on the variables.
Getting it unstuck requires [propositional equality](../type-classes/standard-classes.md#equality-and-ordering).

## Propositional Equality

Propositional equality is the mathematical statement that two expressions are equal.
While definitional equality is a kind of ambient fact that Lean automatically checks when required, statements of propositional equality require explicit proofs.
Once an equality proposition has been proved, it can be used in a program to modify a type, replacing one side of the equality with the other, which can unstick the type checker.

The reason why definitional equality is so limited is to enable it to be checked by an algorithm.
Propositional equality is much richer, but the computer cannot in general check whether two expressions are propositionally equal, though it can verify that a purported proof is in fact a proof.
The split between definitional and propositional equality represents a division of labor between humans and machines: the most boring equalities are checked automatically as part of definitional equality, freeing the human mind to work on the interesting problems available in propositional equality.
Similarly, definitional equality is invoked automatically by the type checker, while propositional equality must be specifically appealed to.


In [Propositions, Proofs, and Indexing](../props-proofs-indexing.md), some equality statements are proved using `simp`.
All of these equality statements are ones in which the propositional equality is in fact already a definitional equality.
Typically, statements of propositional equality are proved by first getting them into a form where they are either definitional or close enough to existing proved equalities, and then using tools like `simp` to take care of the simplified cases.
The `simp` tactic is quite powerful: behind the scenes, it uses a number of fast, automated tools to construct a proof.
A simpler tactic called `rfl` specifically uses definitional equality to prove propositional equality.
The name `rfl` is short for _reflexivity_, which is the property of equality that states that everything equals itself.

Unsticking `appendR` requires a proof that `k = Nat.plusR 0 k`, which is not a definitional equality because `plusR` is stuck on the variable in its second argument.
To get it to compute, the `k` must become a concrete constructor.
This is a job for pattern matching.

In particular, because `k` could be _any_ `Nat`, this task requires a function that can return evidence that `k = Nat.plusR 0 k` for _any_ `k` whatsoever.
This should be a function that returns a proof of equality, with type `(k : Nat) → k = Nat.plusR 0 k`.
Getting it started with initial patterns and placeholders yields the following messages:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean plusR_zero_left1}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean plusR_zero_left1}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean plusR_zero_left2}}
```
Having refined `k` to `0` via pattern matching, the first placeholder stands for evidence of a statement that does hold definitionally.
The `rfl` tactic takes care of it, leaving only the second placeholder:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean plusR_zero_left3}}
```

The second placeholder is a bit trickier.
The expression `{{#example_in Examples/DependentTypes/Pitfalls.lean plusRStep}}` is definitionally equal to `{{#example_out Examples/DependentTypes/Pitfalls.lean plusRStep}}`.
This means that the goal could also be written `k + 1 = Nat.plusR 0 k + 1`:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean plusR_zero_left4}}
```
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean plusR_zero_left4}}
```

Underneath the `+ 1` on each side of the equality statement is another instance of what the function itself returns.
In other words, a recursive call on `k` would return evidence that `k = Nat.plusR 0 k`.
Equality wouldn't be equality if it didn't apply to function arguments. 
In other words, if `x = y`, then `f x = f y`.
The standard library contains a function `congrArg` that takes a function and an equality proof and returns a new proof where the function has been applied to both sides of the equality.
In this case, the function is `(· + 1)`:
```lean
{{#example_decl Examples/DependentTypes/Pitfalls.lean plusR_zero_left_done}}
```

Propositional equalities can be deployed in a program using the rightward triangle operator `▸`.
Given an equality proof as its first argument and some other expression as its second, this operator replaces instances of the left side of the equality with the right side of the equality in the second argument's type.
In other words, the following definition contains no type errors:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean appendRsubst}}
```
The first placeholder has the expected type:
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendRsubst}}
```
It can now be filled in with `ys`:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean appendR5}}
```

Filling in the remaining placeholder requires unsticking another instance of addition:
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean appendR5}}
```
Here, the statement to be proved is that `Nat.plusR (n + 1) k = Nat.plusR n k + 1`, which can be used with `▸` to draw the `+ 1` out to the top of the expression so that it matches the index of `cons`.

The proof is a recursive function that pattern matches on the second argument to `plusR`, namely `k`.
This is because `plusR` itself pattern matches on its second argument, so the proof can "unstick" it through pattern matching, exposing the computational behavior.
The skeleton of the proof is very similar to that of `plusR_zero_left`:
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean plusR_succ_left_0}}
```

The remaining case's type is definitionally equal to `Nat.plusR (n + 1) k + 1 = Nat.plusR n (k + 1) + 1`, so it can be solved with `congrArg`, just as in `plusR_zero_left`:
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean plusR_succ_left_2}}
```
This results in a finished proof:
```lean
{{#example_decl Examples/DependentTypes/Pitfalls.lean plusR_succ_left}}
```

The finished proof can be used to unstick the second case in `appendR`:
```lean
{{#example_decl Examples/DependentTypes/Pitfalls.lean appendR}}
```
When making the length arguments to `appendR` implicit again, they are no longer explicitly named to be appealed to in the proofs.
However, Lean's type checker has enough information to fill them in automatically behind the scenes, because no other values would allow the types to match:
```lean
{{#example_decl Examples/DependentTypes/Pitfalls.lean appendRImpl}}
```

## Pros and Cons

Indexed families have an important property: pattern matching on them affects definitional equality.
For example, in the `nil` case in a `match` expression on a `Vect`, the length simply _becomes_ `0`.
Definitional equality can be very convenient, because it is always active and does not need to be invoked explicitly.

However, the use of definitional equality with dependent types and pattern matching has serious software engineering drawbacks.
First off, functions must be written especially to be used in types, and functions that are convenient to use in types may not use the most efficient algorithms.
Once a function has been exposed through using it in a type, its implementation has become part of the interface, leading to difficulties in future refactoring.
Secondly, definitional equality can be slow.
When asked to check whether two expressions are definitionally equal, Lean may need to run large amounts of code if the functions in question are complicated and have many layers of abstraction.
Third, error messages that result from failures of definitional equality are not always very easy to understand, because they may be phrased in terms of the internals of functions.
It is not always easy to understand the provenance of the expressions in the error messages.
Finally, encoding non-trivial invariants in a collection of indexed families and dependently-typed functions can often be brittle.
It is often necessary to change early definitions in a system when the exposed reduction behavior of functions proves to not provide convenient definitional equalities.
The alternative is to litter the program with appeals to equality proofs, but these can become quite unwieldy.

In idiomatic Lean code, indexed datatypes are not used very often.
Instead, subtypes and explicit propositions are typically used to enforce important invariants.
This approach involves many explicit proofs, and very few appeals to definitional equality.
As befits an interactive theorem prover, Lean has been designed to make explicit proofs convenient.
Generally speaking, this approach should be preferred in most cases.

However, understanding indexed families of datatypes is important.
Recursive functions such as `plusR_zero_left` and `plusR_succ_left` are in fact _proofs by mathematical induction_.
The base case of the recursion corresponds to the base case in induction, and the recursive call represents an appeal to the induction hypothesis.
More generally, new propositions in Lean are often defined as inductive types of evidence, and these inductive types usually have indices.
The process of proving theorems is in fact constructing expressions with these types behind the scenes, in a process not unlike the proofs in this section.
Also, indexed datatypes are sometimes exactly the right tool for the job.
Fluency in their use is an important part of knowing when to use them.



## Exercises

 * Using a recursive function in the style of `plusR_succ_left`, prove that for all `Nat`s `n` and `k`, `n.plusR k = n + k`.
 * Write a function on `Vect` for which `plusR` is more natural than `plusL`, where `plusL` would require proofs to be used in the definition.

