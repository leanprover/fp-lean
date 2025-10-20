import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.Pitfalls"

#doc (Manual) "Pitfalls of Programming with Dependent Types" =>
%%%
tag := "dependent-type-pitfalls"
%%%

The flexibility of dependent types allows more useful programs to be accepted by a type checker, because the language of types is expressive enough to describe variations that less-expressive type systems cannot.
At the same time, the ability of dependent types to express very fine-grained specifications allows more buggy programs to be rejected by a type checker.
This power comes at a cost.

The close coupling between the internals of type-returning functions such as {anchorName Row (module:=Examples.DependentTypes.DB)}`Row` and the types that they produce is an instance of a bigger difficulty: the distinction between the interface and the implementation of functions begins to break down when functions are used in types.
Normally, all refactorings are valid as long as they don't change the type signature or input-output behavior of a function.
Functions can be rewritten to use more efficient algorithms and data structures, bugs can be fixed, and code clarity can be improved without breaking client code.
When the function is used in a type, however, the internals of the function's implementation become part of the type, and thus part of the _interface_ to another program.

As an example, take the following two implementations of addition on {anchorName plusL}`Nat`.
{anchorName plusL}`Nat.plusL` is recursive on its first argument:

```anchor plusL
def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1
```
{anchorName plusR}`Nat.plusR`, on the other hand, is recursive on its second argument:

```anchor plusR
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
```
Both implementations of addition are faithful to the underlying mathematical concept, and they thus return the same result when given the same arguments.

However, these two implementations present quite different interfaces when they are used in types.
As an example, take a function that appends two {anchorName appendL}`Vect`s.
This function should return a {anchorName appendL}`Vect` whose length is the sum of the length of the arguments.
Because {anchorName appendL}`Vect` is essentially a {anchorName moreNames}`List` with a more informative type, it makes sense to write the function just as one would for {anchorName moreNames}`List.append`, with pattern matching and recursion on the first argument.
Starting with a type signature and initial pattern match pointing at placeholders yields two messages:
```anchor appendL1
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => _
  | .cons x xs, ys => _
```
The first message, in the {anchorName moreNames}`nil` case, states that the placeholder should be replaced by a {anchorName appendL}`Vect` with length {lit}`plusL 0 k`:
```anchorError appendL1
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
```
The second message, in the {anchorName moreNames}`cons` case, states that the placeholder should be replaced by a {anchorName appendL}`Vect` with length {lit}`plusL (n✝ + 1) k`:
```anchorError appendL2
don't know how to synthesize placeholder
context:
α : Type u_1
n k n✝ : Nat
x : α
xs : Vect α n✝
ys : Vect α k
⊢ Vect α ((n✝ + 1).plusL k)
```
The symbol after {lit}`n`, called a _dagger_, is used to indicate names that Lean has internally invented.
Behind the scenes, pattern matching on the first {anchorName appendL1}`Vect` implicitly caused the value of the first {anchorName plusL}`Nat` to be refined as well, because the index on the constructor {anchorName moreNames}`cons` is {anchorTerm Vect (module:=Examples.DependentTypes)}`n + 1`, with the tail of the {anchorName appendL}`Vect` having length {anchorTerm Vect (module:=Examples.DependentTypes)}`n`.
Here, {lit}`n✝` represents the {anchorName moreNames}`Nat` that is one less than the argument {anchorName appendL1}`n`.

# Definitional Equality
%%%
tag := "definitional-equality"
%%%

In the definition of {anchorName appendL3}`plusL`, there is a pattern case {anchorTerm plusL}`0, k => k`.
This applies in the length used in the first placeholder, so another way to write the underscore's type {anchorTerm moreNames}`Vect α (Nat.plusL 0 k)` is {anchorTerm moreNames}`Vect α k`.
Similarly, {anchorName plusL}`plusL` contains a pattern case {anchorTerm plusL}`n + 1, k => plusL n k + 1`.
This means that the type of the second underscore can be equivalently written {lit}`Vect α (plusL n✝ k + 1)`.

To expose what is going on behind the scenes, the first step is to write the {anchorName plusL}`Nat` arguments explicitly, which also results in daggerless error messages because the names are now written explicitly in the program:
```anchor appendL3
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendL3
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
```
```anchorError appendL4
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusL k)
```
Annotating the underscores with the simplified versions of the types does not introduce a type error, which means that the types as written in the program are equivalent to the ones that Lean found on its own:
```anchor appendL5
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
```
```anchorError appendL5
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k
```
```anchorError appendL6
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k + 1)
```

The first case demands a {anchorTerm appendL5}`Vect α k`, and {anchorName appendL5}`ys` has that type.
This is parallel to the way that appending the empty list to any other list returns that other list.
Refining the definition with {anchorName appendL7}`ys` instead of the first underscore yields a program with only one remaining underscore to be filled out:
```anchor appendL7
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
```
```anchorError appendL7
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k + 1)
```

Something very important has happened here.
In a context where Lean expected a {anchorTerm moreNames}`Vect α (Nat.plusL 0 k)`, it received a {anchorTerm moreNames}`Vect α k`.
However, {anchorName plusL}`Nat.plusL` is not an {kw}`abbrev`, so it may seem like it shouldn't be running during type checking.
Something else is happening.

The key to understanding what's going on is that Lean doesn't just expand {kw}`abbrev`s while type checking.
It can also perform computation while checking whether two types are equivalent to one another, such that any expression of one type can be used in a context that expects the other type.
This property is called _definitional equality_, and it is subtle.

Certainly, two types that are written identically are considered to be definitionally equal—{anchorName moreNames}`Nat` and {anchorName moreNames}`Nat` or {anchorTerm moreNames}`List String` and {anchorTerm moreNames}`List String` should be considered equal.
Any two concrete types built from different datatypes are not equal, so {anchorTerm moreNames}`List Nat` is not equal to {anchorName moreNames}`Int`.
Additionally, types that differ only by renaming internal names are equal, so {anchorTerm moreNames}`(n : Nat) → Vect String n` is the same as {anchorTerm moreNames}`(k : Nat) → Vect String k`.
Because types can contain ordinary data, definitional equality must also describe when data are equal.
Uses of the same constructors are equal, so {anchorTerm moreNames}`0` equals {anchorTerm moreNames}`0` and {anchorTerm moreNames}`[5, 3, 1]` equals {anchorTerm moreNames}`[5, 3, 1]`.

Types contain more than just function arrows, datatypes, and constructors, however.
They also contain _variables_ and _functions_.
Definitional equality of variables is relatively simple: each variable is equal only to itself, so {anchorTerm moreNames}`(n k : Nat) → Vect Int n` is not definitionally equal to {anchorTerm moreNames}`(n k : Nat) → Vect Int k`.
Functions, on the other hand, are more complicated.
While mathematics considers two functions to be equal if they have identical input-output behavior, there is no efficient algorithm to check that, and the whole point of definitional equality is for Lean to check whether two types are interchangeable.
Instead, Lean considers functions to be definitionally equal either when they are both {kw}`fun`-expressions with definitionally equal bodies.
In other words, two functions must use _the same algorithm_ that calls _the same helpers_ to be considered definitionally equal.
This is not typically very helpful, so definitional equality of functions is mostly used when the exact same defined function occurs in two types.

When functions are _called_ in a type, checking definitional equality may involve reducing the function call.
The type {anchorTerm moreNames}`Vect String (1 + 4)` is definitionally equal to the type {anchorTerm moreNames}`Vect String (3 + 2)` because {anchorTerm moreNames}`1 + 4` is definitionally equal to {anchorTerm moreNames}`3 + 2`.
To check their equality, both are reduced to {anchorTerm moreNames}`5`, and then the constructor rule can be used five times.
Definitional equality of functions applied to data can be checked first by seeing if they're already the same—there's no need to reduce {anchorTerm moreNames}`["a", "b"] ++ ["c"]` to check that it's equal to {anchorTerm moreNames}`["a", "b"] ++ ["c"]`, after all.
If not, the function is called and replaced with its value, and the value can then be checked.

Not all function arguments are concrete data.
For example, types may contain {anchorName moreNames}`Nat`s that are not built from the {anchorName moreNames}`zero` and {anchorName moreNames}`succ` constructors.
In the type {anchorTerm moreFun}`(n : Nat) → Vect String n`, the variable {anchorName moreFun}`n` is a {anchorName moreFun}`Nat`, but it is impossible to know _which_ {anchorName moreFun}`Nat` it is before the function is called.
Indeed, the function may be called first with {anchorTerm moreNames}`0`, and then later with {anchorTerm moreNames}`17`, and then again with {anchorTerm moreNames}`33`.
As seen in the definition of {anchorName appendL}`appendL`, variables with type {anchorName moreFun}`Nat` may also be passed to functions such as {anchorName appendL}`plusL`.
Indeed, the type {anchorTerm moreFun}`(n : Nat) → Vect String n` is definitionally equal to the type {anchorTerm moreNames}`(n : Nat) → Vect String (Nat.plusL 0 n)`.

The reason that {anchorName againFun}`n` and {anchorTerm againFun}`Nat.plusL 0 n` are definitionally equal is that {anchorName plusL}`plusL`'s pattern match examines its _first_ argument.
This is problematic: {anchorTerm moreFun}`(n : Nat) → Vect String n` is _not_ definitionally equal to {anchorTerm stuckFun}`(n : Nat) → Vect String (Nat.plusL n 0)`, even though zero should be both a left and a right identity of addition.
This happens because pattern matching gets stuck when it encounters variables.
Until the actual value of {anchorName stuckFun}`n` becomes known, there is no way to know which case of {anchorTerm stuckFun}`Nat.plusL n 0` should be selected.

The same issue appears with the {anchorName Row (module:=Examples.DependentTypes.DB)}`Row` function in the query example.
The type {anchorTerm RowStuck (module:=Examples.DependentTypes.DB)}`Row (c :: cs)` does not reduce to any datatype because the definition of {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row` has separate cases for singleton lists and lists with at least two entries.
In other words, it gets stuck when trying to match the variable {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`cs` against concrete {anchorName moreNames}`List` constructors.
This is why almost every function that takes apart or constructs a {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row` needs to match the same three cases as {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row` itself: getting it unstuck reveals concrete types that can be used for either pattern matching or constructors.

The missing case in {anchorName appendL8}`appendL` requires a {lit}`Vect α (Nat.plusL n k + 1)`.
The {lit}`+ 1` in the index suggests that the next step is to use {anchorName consNotLengthN (module:=Examples.DependentTypes)}`Vect.cons`:
```anchor appendL8
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (_ : Vect α (n.plusL k))
```
```anchorError appendL8
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k)
```
A recursive call to {anchorName appendL9}`appendL` can construct a {anchorName appendL9}`Vect` with the desired length:

```anchor appendL9
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (appendL n k xs ys)
```
Now that the program is finished, removing the explicit matching on {anchorName appendL9}`n` and {anchorName appendL9}`k` makes it easier to read and easier to call the function:

```anchor appendL
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendL xs ys)
```

Comparing types using definitional equality means that everything involved in definitional equality, including the internals of function definitions, becomes part of the _interface_ of programs that use dependent types and indexed families.
Exposing the internals of a function in a type means that refactoring the exposed program may cause programs that use it to no longer type check.
In particular, the fact that {anchorName appendL}`plusL` is used in the type of {anchorName appendL}`appendL` means that the definition of {anchorName appendL}`plusL` cannot be replaced by the otherwise-equivalent {anchorName plusR}`plusR`.

# Getting Stuck on Addition
%%%
tag := "stuck-addition"
%%%

What happens if append is defined with {anchorName appendR}`plusR` instead?
Beginning in the same way, with explicit lengths and placeholder underscores in each case, reveals the following useful error messages:
```anchor appendR1
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendR1
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusR 0 k)
```
```anchorError appendR2
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusR k)
```
However, attempting to place a {anchorTerm appendR3}`Vect α k` type annotation around the first placeholder results in an type mismatch error:
```anchor appendR3
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendR3
Type mismatch
  ?m.11
has type
  Vect α k
but is expected to have type
  Vect α (Nat.plusR 0 k)
```
This error is pointing out that {anchorTerm plusRinfo}`Nat.plusR 0 k` and {anchorName plusRinfo}`k` are _not_ definitionally equal.

:::paragraph
This is because {anchorName plusR}`plusR` has the following definition:

```anchor plusR
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
```
Its pattern matching occurs on the _second_ argument, not the first argument, which means that the presence of the variable {anchorName plusRinfo}`k` in that position prevents it from reducing.
{anchorName plusRinfo}`Nat.add` in Lean's standard library is equivalent to {anchorName plusRinfo}`plusR`, not {anchorName plusRinfo}`plusL`, so attempting to use it in this definition results in precisely the same difficulties:
```anchor appendR4
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n + k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendR4
Type mismatch
  ?m.15
has type
  Vect α k
but is expected to have type
  Vect α (0 + k)
```

Addition is getting _stuck_ on the variables.
Getting it unstuck requires {ref "equality-and-ordering"}[propositional equality].
:::

# Propositional Equality
%%%
tag := "propositional-equality"
%%%

Propositional equality is the mathematical statement that two expressions are equal.
While definitional equality is a kind of ambient fact that Lean automatically checks when required, statements of propositional equality require explicit proofs.
Once an equality proposition has been proved, it can be used in a program to modify a type, replacing one side of the equality with the other, which can unstick the type checker.

The reason why definitional equality is so limited is to enable it to be checked by an algorithm.
Propositional equality is much richer, but the computer cannot in general check whether two expressions are propositionally equal, though it can verify that a purported proof is in fact a proof.
The split between definitional and propositional equality represents a division of labor between humans and machines: the most boring equalities are checked automatically as part of definitional equality, freeing the human mind to work on the interesting problems available in propositional equality.
Similarly, definitional equality is invoked automatically by the type checker, while propositional equality must be specifically appealed to.


In {ref "props-proofs-indexing"}[Propositions, Proofs, and Indexing], some equality statements are proved using {tactic}`decide`.
All of these equality statements are ones in which the propositional equality is in fact already a definitional equality.
Typically, statements of propositional equality are proved by first getting them into a form where they are either definitional or close enough to existing proved equalities, and then using tools like {tactic}`decide` or {tactic}`simp` to take care of the simplified cases.
The {tactic}`simp` tactic is quite powerful: behind the scenes, it uses a number of fast, automated tools to construct a proof.
A simpler tactic called {kw}`rfl` specifically uses definitional equality to prove propositional equality.
The name {kw}`rfl` is short for _reflexivity_, which is the property of equality that states that everything equals itself.

Unsticking {anchorName appendR}`appendR` requires a proof that {anchorTerm plusR_zero_left1}`k = Nat.plusR 0 k`, which is not a definitional equality because {anchorName plusR}`plusR` is stuck on the variable in its second argument.
To get it to compute, the {anchorName plusR_zero_left1}`k` must become a concrete constructor.
This is a job for pattern matching.

:::paragraph
In particular, because {anchorName plusR_zero_left1}`k` could be _any_ {anchorName plusR_zero_left1}`Nat`, this task requires a function that can return evidence that {anchorTerm plusR_zero_left1}`k = Nat.plusR 0 k` for _any_ {anchorName plusR_zero_left1}`k` whatsoever.
This should be a function that returns a proof of equality, with type {anchorTerm plusR_zero_left1}`(k : Nat) → k = Nat.plusR 0 k`.
Getting it started with initial patterns and placeholders yields the following messages:
```anchor plusR_zero_left1
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => _
  | k + 1 => _
```
```anchorError plusR_zero_left1
don't know how to synthesize placeholder
context:
⊢ 0 = Nat.plusR 0 0
```
```anchorError plusR_zero_left2
don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 (k + 1)
```
Having refined {anchorName plusR_zero_left1}`k` to {anchorTerm plusR_zero_left1}`0` via pattern matching, the first placeholder stands for evidence of a statement that does hold definitionally.
The {kw}`rfl` tactic takes care of it, leaving only the second placeholder:
```anchor plusR_zero_left3
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 => _
```
:::

The second placeholder is a bit trickier.
The expression {anchorTerm plusRStep}`Nat.plusR 0 k + 1` is definitionally equal to {anchorTerm plusRStep}`Nat.plusR 0 (k + 1)`.
This means that the goal could also be written {anchorTerm plusR_zero_left4}`k + 1 = Nat.plusR 0 k + 1`:
```anchor plusR_zero_left4
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 => (_ : k + 1 = Nat.plusR 0 k + 1)
```
```anchorError plusR_zero_left4
don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 k + 1
```

:::paragraph
Underneath the {anchorTerm plusR_zero_left4}`+ 1` on each side of the equality statement is another instance of what the function itself returns.
In other words, a recursive call on {anchorName plusR_zero_left4}`k` would return evidence that {anchorTerm plusR_zero_left4}`k = Nat.plusR 0 k`.
Equality wouldn't be equality if it didn't apply to function arguments.
In other words, if {anchorTerm congr}`x = y`, then {anchorTerm congr}`f x = f y`.
The standard library contains a function {anchorName congr}`congrArg` that takes a function and an equality proof and returns a new proof where the function has been applied to both sides of the equality.
In this case, the function is {anchorTerm plusR_zero_left_done}`(· + 1)`:

```anchor plusR_zero_left_done
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
```
:::

:::paragraph
Because this is really a proof of a proposition, it should be declared as a {kw}`theorem`:

```anchor plusR_zero_left_thm
theorem plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
```
:::

Propositional equalities can be deployed in a program using the rightward triangle operator {anchorTerm appendRsubst}`▸`.
Given an equality proof as its first argument and some other expression as its second, this operator replaces instances of one side of the equality with the other side of the equality in the second argument's type.
In other words, the following definition contains no type errors:
```anchor appendRsubst
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
```
The first placeholder has the expected type:
```anchorError appendRsubst
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k
```
It can now be filled in with {anchorName appendR5}`ys`:
```anchor appendR5
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys => _
```

Filling in the remaining placeholder requires unsticking another instance of addition:
```anchorError appendR5
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusR k)
```
Here, the statement to be proved is that {anchorTerm plusR_succ_left}`Nat.plusR (n + 1) k = Nat.plusR n k + 1`, which can be used with {anchorTerm appendRsubst}`▸` to draw the {anchorTerm appendRsubst}`+ 1` out to the top of the expression so that it matches the index of {anchorName Vect}`cons`.

The proof is a recursive function that pattern matches on the second argument to {anchorName appendR}`plusR`, namely {anchorName appendR5}`k`.
This is because {anchorName appendR5}`plusR` itself pattern matches on its second argument, so the proof can “unstick” it through pattern matching, exposing the computational behavior.
The skeleton of the proof is very similar to that of {anchorName appendR}`plusR_zero_left`:
```anchor plusR_succ_left_0
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => _
```

The remaining case's type is definitionally equal to {anchorTerm congr}`Nat.plusR (n + 1) k + 1 = Nat.plusR n (k + 1) + 1`, so it can be solved with {anchorName congr}`congrArg`, just as in {anchorName plusR_zero_left_thm}`plusR_zero_left`:
```anchorError plusR_succ_left_2
don't know how to synthesize placeholder
context:
n k : Nat
⊢ (n + 1).plusR (k + 1) = n.plusR (k + 1) + 1
```
This results in a finished proof:

```anchor plusR_succ_left
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)
```

The finished proof can be used to unstick the second case in {anchorName appendR}`appendR`:

```anchor appendR
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys =>
    plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys =>
    plusR_succ_left n k ▸ .cons x (appendR n k xs ys)
```
When making the length arguments to {anchorName appendR}`appendR` implicit again, they are no longer explicitly named to be appealed to in the proofs.
However, Lean's type checker has enough information to fill them in automatically behind the scenes, because no other values would allow the types to match:

```anchor appendRImpl
def appendR : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys => plusR_zero_left _ ▸ ys
  | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR xs ys)
```

# Pros and Cons
%%%
tag := "dependent-types-pros-and-cons"
%%%

Indexed families have an important property: pattern matching on them affects definitional equality.
For example, in the {anchorName Vect}`nil` case in a {kw}`match` expression on a {anchorTerm Vect}`Vect`, the length simply _becomes_ {anchorTerm moreNames}`0`.
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
Recursive functions such as {anchorName plusR_zero_left_thm}`plusR_zero_left` and {anchorName plusR_succ_left}`plusR_succ_left` are in fact _proofs by mathematical induction_.
The base case of the recursion corresponds to the base case in induction, and the recursive call represents an appeal to the induction hypothesis.
More generally, new propositions in Lean are often defined as inductive types of evidence, and these inductive types usually have indices.
The process of proving theorems is in fact constructing expressions with these types behind the scenes, in a process not unlike the proofs in this section.
Also, indexed datatypes are sometimes exactly the right tool for the job.
Fluency in their use is an important part of knowing when to use them.



# Exercises
%%%
tag := "dependent-type-pitfalls-exercises"
%%%

 * Using a recursive function in the style of {anchorName plusR_succ_left}`plusR_succ_left`, prove that for all {anchorName moreNames}`Nat`s {anchorName exercises}`n` and {anchorName exercises}`k`, {anchorTerm exercises}`n.plusR k = n + k`.
 * Write a function on {anchorName moreNames}`Vect` for which {anchorName plusR}`plusR` is more natural than {anchorName plusL}`plusL`, where {anchorName plusL}`plusL` would require proofs to be used in the definition.
