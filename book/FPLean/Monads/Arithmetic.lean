import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "Example: Arithmetic in Monads" =>
%%%
tag := "monads-arithmetic-example"
%%%

Monads are a way of encoding programs with side effects into a language that does not have them.
It would be easy to read this as a sort of admission that pure functional programs are missing something important, requiring programmers to jump through hoops just to write a normal program.
However, while using the {moduleName}`Monad` API does impose a syntactic cost on a program, it brings two important benefits:
 1. Programs must be honest about which effects they use in their types. A quick glance at a type signature describes _everything_ that the program can do, rather than just what it accepts and what it returns.
 2. Not every language provides the same effects. For example, only some languages have exceptions. Other languages have unique, exotic effects, such as [Icon's searching over multiple values](https://www2.cs.arizona.edu/icon/) and Scheme or Ruby's continuations. Because monads can encode _any_ effect, programmers can choose which ones are the best fit for a given application, rather than being stuck with what the language developers provided.

One example of a program that can make sense in a variety of monads is an evaluator for arithmetic expressions.

# Arithmetic Expressions
%%%
tag := "monads-arithmetic-example-expr"
%%%

:::paragraph
An arithmetic expression is either a literal integer or a primitive binary operator applied to two expressions. The operators are addition, subtraction, multiplication, and division:

```anchor ExprArith
inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op


inductive Arith where
  | plus
  | minus
  | times
  | div
```
:::

:::paragraph
The expression {lit}`2 + 3` is represented:

```anchor twoPlusThree
open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)
```
and {lit}`14 / (45 - 5 * 9)` is represented:
```anchor exampleArithExpr
open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 14)
    (prim minus (const 45)
      (prim times (const 5)
        (const 9)))
```
:::

# Evaluating Expressions
%%%
tag := "monads-arithmetic-example-eval"
%%%

:::paragraph
Because expressions include division, and division by zero is undefined, evaluation might fail.
One way to represent failure is to use {anchorName evaluateOptionCommingled}`Option`:

```anchor evaluateOptionCommingled
def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    match p with
    | Arith.plus => pure (v1 + v2)
    | Arith.minus => pure (v1 - v2)
    | Arith.times => pure (v1 * v2)
    | Arith.div => if v2 == 0 then none else pure (v1 / v2)
```
:::

:::paragraph
This definition uses the {anchorTerm MonadOptionExcept}`Monad Option` instance to propagate failures from evaluating both branches of a binary operator.
However, the function mixes two concerns: evaluating subexpressions and applying a binary operator to the results.
It can be improved by splitting it into two functions:

```anchor evaluateOptionSplit
def applyPrim : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => if y == 0 then none else pure (x / y)

def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    applyPrim p v1 v2
```
:::

:::paragraph
Running {anchorTerm fourteenDivOption}`#eval evaluateOption fourteenDivided` yields {anchorInfo fourteenDivOption}`none`, as expected, but this is not a very useful error message.
Because the code was written using {lit}`>>=` rather than by explicitly handling the {anchorName MonadOptionExcept}`none` constructor, only a small modification is required for it to provide an error message on failure:

```anchor evaluateExcept
def applyPrim : Arith → Int → Int → Except String Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateExcept : Expr Arith → Except String Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateExcept e1 >>= fun v1 =>
    evaluateExcept e2 >>= fun v2 =>
    applyPrim p v1 v2
```
The only difference is that the type signature mentions {anchorTerm evaluateExcept}`Except String` instead of {anchorName Names}`Option`, and the failing case uses {anchorName evaluateExcept}`Except.error` instead of {anchorName evaluateM}`none`.
By making the evaluator polymorphic over its monad and passing it {anchorName evaluateM}`applyPrim` as an argument, a single evaluator becomes capable of both forms of error reporting:

```anchor evaluateM
def applyPrimOption : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      none
    else pure (x / y)

def applyPrimExcept : Arith → Int → Int → Except String Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateM [Monad m]
    (applyPrim : Arith → Int → Int → m Int) :
    Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2
```
:::

Using it with {anchorName evaluateMOption}`applyPrimOption` works just like the first evaluator:
```anchor evaluateMOption
#eval evaluateM applyPrimOption fourteenDivided
```
```anchorInfo evaluateMOption
none
```
Similarly, using it with {anchorName evaluateMExcept}`applyPrimExcept` works just like the version with error messages:
```anchor evaluateMExcept
#eval evaluateM applyPrimExcept fourteenDivided
```
```anchorInfo evaluateMExcept
Except.error "Tried to divide 14 by zero"
```

:::paragraph
The code can still be improved.
The functions {anchorName evaluateMOption}`applyPrimOption` and {anchorName evaluateMExcept}`applyPrimExcept` differ only in their treatment of division, which can be extracted into another parameter to the evaluator:

```anchor evaluateMRefactored
def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then
      none
    else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m]
    (applyDiv : Int → Int → m Int) :
    Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

def evaluateM [Monad m]
    (applyDiv : Int → Int → m Int) :
    Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyDiv e1 >>= fun v1 =>
    evaluateM applyDiv e2 >>= fun v2 =>
    applyPrim applyDiv p v1 v2
```

In this refactored code, the fact that the two code paths differ only in their treatment of failure has been made fully apparent.
:::

# Further Effects
%%%
tag := "monads-arithmetic-example-effects"
%%%

Failure and exceptions are not the only kinds of effects that can be interesting when working with an evaluator.
While division's only side effect is failure, adding other primitive operators to the expressions make it possible to express other effects.

The first step is an additional refactoring, extracting division from the datatype of primitives:

```anchor PrimCanFail
inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div
```
The name {anchorName PrimCanFail}`CanFail` suggests that the effect introduced by division is potential failure.

The second step is to broaden the scope of the division handler argument to {anchorName evaluateMMorePoly}`evaluateM` so that it can process any special operator:

```anchor evaluateMMorePoly
def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2
```

## No Effects
%%%
tag := "monads-arithmetic-example-no-effects"
%%%

The type {anchorName applyEmpty}`Empty` has no constructors, and thus no values, like the {Kotlin}`Nothing` type in Scala or Kotlin.
In Scala and Kotlin, {Kotlin}`Nothing` can represent computations that never return a result, such as functions that crash the program, throw exceptions, or always fall into infinite loops.
An argument to a function or method of type {Kotlin}`Nothing` indicates dead code, as there will never be a suitable argument value.
Lean doesn't support infinite loops and exceptions, but {anchorName applyEmpty}`Empty` is still useful as an indication to the type system that a function cannot be called.
Using the syntax {anchorTerm nomatch}`nomatch E` when {anchorName nomatch}`E` is an expression whose type has no constructors indicates to Lean that the current expression need not return a result, because it could never have been called.

Using {anchorName applyEmpty}`Empty` as the parameter to {anchorName PrimCanFail}`Prim` indicates that there are no additional cases beyond {anchorName evaluateMMorePoly}`Prim.plus`, {anchorName evaluateMMorePoly}`Prim.minus`, and {anchorName evaluateMMorePoly}`Prim.times`, because it is impossible to come up with a value of type {anchorName nomatch}`Empty` to place in the {anchorName evaluateMMorePoly}`Prim.other` constructor.
Because a function to apply an operator of type {anchorName nomatch}`Empty` to two integers can never be called, it doesn't need to return a result.
Thus, it can be used in _any_ monad:

```anchor applyEmpty
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op
```
This can be used together with {anchorName evalId}`Id`, the identity monad, to evaluate expressions that have no effects whatsoever:
```anchor evalId
open Expr Prim in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))
```
```anchorInfo evalId
-9
```

## Nondeterministic Search
%%%
tag := "nondeterministic-search"
%%%

Instead of simply failing when encountering division by zero, it would also be sensible to backtrack and try a different input.
Given the right monad, the very same {anchorName evalId}`evaluateM` can perform a nondeterministic search for a _set_ of answers that do not result in failure.
This requires, in addition to division, some means of specifying a choice of results.
One way to do this is to add a function {lit}`choose` to the language of expressions that instructs the evaluator to pick either of its arguments while searching for non-failing results.

The result of the evaluator is now a multiset of values, rather than a single value.
The rules for evaluation into a multiset are:
 * Constants $`n` evaluate to singleton sets $`\{n\}`.
 * Arithmetic operators other than division are called on each pair from the Cartesian product of the operators, so $`X + Y` evaluates to $`\{ x + y \mid x ∈ X, y ∈ Y \}`.
 * Division $`X / Y` evaluates to $`\{ x / y \mid x ∈ X, y ∈ Y, y ≠ 0\}`. In other words, all $`0` values in $`Y`  are thrown out.
 * A choice $`\mathrm{choose}(x, y)` evaluates to $`\{ x, y \}`.

For example, $`1 + \mathrm{choose}(2, 5)` evaluates to $`\{ 3, 6 \}`, $`1 + 2 / 0` evaluates to $`\{\}`, and $`90 / (\mathrm{choose}(-5, 5) + 5)` evaluates to $`\{ 9 \}`.
Using multisets instead of true sets simplifies the code by removing the need to check for uniqueness of elements.

:::paragraph
A monad that represents this non-deterministic effect must be able to represent a situation in which there are no answers, and a situation in which there is at least one answer together with any remaining answers:

```anchor Many (module := Examples.Monads.Many)
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α
```
This datatype looks very much like {anchorName fromList (module:=Examples.Monads.Many)}`List`.
The difference is that where {anchorName etc}`List.cons` stores the rest of the list, {anchorName Many (module:=Examples.Monads.Many)}`more` stores a function that should compute the remaining values on demand.
This means that a consumer of {anchorName Many (module:=Examples.Monads.Many)}`Many` can stop the search when some number of results have been found.
:::

:::paragraph
A single result is represented by a {anchorName Many (module:=Examples.Monads.Many)}`more` constructor that returns no further results:

```anchor one (module := Examples.Monads.Many)
def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)
```
:::

:::paragraph
The union of two multisets of results can be computed by checking whether the first multiset is empty.
If so, the second multiset is the union.
If not, the union consists of the first element of the first multiset followed by the union of the rest of the first multiset with the second multiset:

```anchor union (module := Examples.Monads.Many)
def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)
```
:::

:::paragraph
It can be convenient to start a search process with a list of values.
{anchorName fromList (module:=Examples.Monads.Many)}`Many.fromList` converts a list into a multiset of results:

```anchor fromList (module := Examples.Monads.Many)
def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)
```

Similarly, once a search has been specified, it can be convenient to extract either a number of values, or all the values:

```anchor take (module := Examples.Monads.Many)
def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll
```
:::

A {anchorTerm MonadMany (module:=Examples.Monads.Many)}`Monad Many` instance requires a {anchorName MonadContract}`bind` operator.
In a nondeterministic search, sequencing two operations consists of taking all possibilities from the first step and running the rest of the program on each of them, taking the union of the results.
In other words, if the first step returns three possible answers, the second step needs to be tried for all three.
Because the second step can return any number of answers for each input, taking their union represents the entire search space.

```anchor bind (module := Examples.Monads.Many)
def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)
```

{anchorName MonadMany (module:=Examples.Monads.Many)}`Many.one` and {anchorName MonadMany (module:=Examples.Monads.Many)}`Many.bind` obey the monad contract.
To check that {anchorTerm bindLeft (module:=Examples.Monads.Many)}`Many.bind (Many.one v) f` is the same as {anchorTerm bindLeft (module:=Examples.Monads.Many)}`f v`, start by evaluating the expression as far as possible:
```anchorEvalSteps bindLeft (module := Examples.Monads.Many)
Many.bind (Many.one v) f
===>
Many.bind (Many.more v (fun () => Many.none)) f
===>
(f v).union (Many.bind Many.none f)
===>
(f v).union Many.none
```
The empty multiset is a right identity of {anchorName union (module:=Examples.Monads.Many)}`union`, so the answer is equivalent to {anchorTerm bindLeft (module:=Examples.Monads.Many)}`f v`.
To check that {anchorTerm bindOne (module:=Examples.Monads.Many)}`Many.bind v Many.one` is the same as {anchorName bindOne (module:=Examples.Monads.Many)}`v`, consider that {anchorName bindOne (module:=Examples.Monads.Many)}`Many.bind` takes the union of applying {anchorName one (module:=Examples.Monads.Many)}`Many.one` to each element of {anchorName bindOne (module:=Examples.Monads.Many)}`v`.
In other words, if {anchorName bindOne (module:=Examples.Monads.Many)}`v` has the form {anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`, then {anchorTerm bindOne (module:=Examples.Monads.Many)}`Many.bind v Many.one` is {anchorTerm vSets (module:=Examples.Monads.Many)}`{v₁} ∪ {v₂} ∪ {v₃} ∪ … ∪ {vₙ}`, which is {anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`.

Finally, to check that {anchorName bind (module:=Examples.Monads.Many)}`Many.bind` is associative, check that {anchorTerm bindBindLeft (module:=Examples.Monads.Many)}`Many.bind (Many.bind v f) g` is the same as {anchorTerm bindBindRight (module:=Examples.Monads.Many)}`Many.bind v (fun x => Many.bind (f x) g)`.
If {anchorName bindBindRight (module:=Examples.Monads.Many)}`v` has the form {anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`, then:
```anchorEvalSteps bindUnion (module := Examples.Monads.Many)
Many.bind v f
===>
f v₁ ∪ f v₂ ∪ f v₃ ∪ … ∪ f vₙ
```
which means that
```anchorEvalSteps bindBindLeft (module := Examples.Monads.Many)
Many.bind (Many.bind v f) g
===>
Many.bind (f v₁) g ∪
Many.bind (f v₂) g ∪
Many.bind (f v₃) g ∪
… ∪
Many.bind (f vₙ) g
```
Similarly,
```anchorEvalSteps bindBindRight (module := Examples.Monads.Many)
Many.bind v (fun x => Many.bind (f x) g)
===>
(fun x => Many.bind (f x) g) v₁ ∪
(fun x => Many.bind (f x) g) v₂ ∪
(fun x => Many.bind (f x) g) v₃ ∪
… ∪
(fun x => Many.bind (f x) g) vₙ
===>
Many.bind (f v₁) g ∪
Many.bind (f v₂) g ∪
Many.bind (f v₃) g ∪
… ∪
Many.bind (f vₙ) g
```
Thus, both sides are equal, so {anchorName bindAssoc (module:=Examples.Monads.Many)}`Many.bind` is associative.

The resulting monad instance is:

```anchor MonadMany (module := Examples.Monads.Many)
instance : Monad Many where
  pure := Many.one
  bind := Many.bind
```
An example search using this monad finds all the combinations of numbers in a list that add to 15:

```anchor addsTo (module := Examples.Monads.Many)
def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
         pure (x :: answer))
```
The search process is recursive over the list.
The empty list is a successful search when the goal is {anchorTerm addsTo (module:=Examples.Monads.Many)}`0`; otherwise, it fails.
When the list is non-empty, there are two possibilities: either the head of the list is greater than the goal, in which case it cannot participate in any successful searches, or it is not, in which case it can.
If the head of the list is _not_ a candidate, then the search proceeds to the tail of the list.
If the head is a candidate, then there are two possibilities to be combined with {anchorName union (module:=Examples.Monads.Many)}`Many.union`: either the solutions found contain the head, or they do not.
The solutions that do not contain the head are found with a recursive call on the tail, while the solutions that do contain it result from subtracting the head from the goal, and then attaching the head to the solutions that result from the recursive call.

The helper {anchorName printList (module:=Examples.Monads.Many)}`printList` ensures that one result is displayed per line:

```anchor printList (module := Examples.Monads.Many)
def printList [ToString α] : List α → IO Unit
  | [] => pure ()
  | x :: xs => do
    IO.println x
    printList xs
```
```anchor addsToFifteen (module := Examples.Monads.Many)
#eval printList (addsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).takeAll
```
```anchorInfo addsToFifteen (module := Examples.Monads.Many)
[7, 8]
[6, 9]
[5, 10]
[4, 5, 6]
[3, 5, 7]
[3, 4, 8]
[2, 6, 7]
[2, 5, 8]
[2, 4, 9]
[2, 3, 10]
[2, 3, 4, 6]
[1, 6, 8]
[1, 5, 9]
[1, 4, 10]
[1, 3, 5, 6]
[1, 3, 4, 7]
[1, 2, 5, 7]
[1, 2, 4, 8]
[1, 2, 3, 9]
[1, 2, 3, 4, 5]
```

:::paragraph
Returning to the arithmetic evaluator that produces multisets of results, the {anchorName NeedsSearch}`choose` operator can be used to nondeterministically select a value, with division by zero rendering prior selections invalid.

```anchor NeedsSearch
inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)
```
:::

:::paragraph
Using these operators, the earlier examples can be evaluated:

```anchor opening
open Expr Prim NeedsSearch
```
```anchor searchA
#eval
  (evaluateM applySearch
    (prim plus (const 1)
      (prim (other choose) (const 2)
        (const 5)))).takeAll
```
```anchorInfo searchA
[3, 6]
```
```anchor searchB
#eval
  (evaluateM applySearch
    (prim plus (const 1)
      (prim (other div) (const 2)
        (const 0)))).takeAll
```
```anchorInfo searchB
[]
```
```anchor searchC
#eval
  (evaluateM applySearch
    (prim (other div) (const 90)
      (prim plus (prim (other choose) (const (-5)) (const 5))
        (const 5)))).takeAll
```
```anchorInfo searchC
[9]
```
:::

## Custom Environments
%%%
tag := "custom-environments"
%%%

The evaluator can be made user-extensible by allowing strings to be used as operators, and then providing a mapping from strings to a function that implements them.
For example, users could extend the evaluator with a remainder operator or with one that returns the maximum of its two arguments.
The mapping from function names to function implementations is called an _environment_.

The environments needs to be passed in each recursive call.
Initially, it might seem that {anchorName evaluateM}`evaluateM` needs an extra argument to hold the environment, and that this argument should be passed to each recursive invocation.
However, passing an argument like this is another form of monad, so an appropriate {anchorName evaluateM}`Monad` instance allows the evaluator to be used unchanged.

Using functions as a monad is typically called a _reader_ monad.
When evaluating expressions in the reader monad, the following rules are used:
 * Constants $`n` evaluate to constant functions $`λ e . n`,
 * Arithmetic operators evaluate to functions that pass their arguments on, so $`f + g` evaluates to $`λ e . f(e) + g(e)`, and
 * Custom operators evaluate to the result of applying the custom operator to the arguments, so $`f \ \mathrm{OP}\ g` evaluates to
   $$`
     λ e .
     \begin{cases}
     h(f(e), g(e)) & \mathrm{if}\ e\ \mathrm{contains}\ (\mathrm{OP}, h) \\
     0 & \mathrm{otherwise}
     \end{cases}
   `
   with $`0` serving as a fallback in case an unknown operator is applied.

:::paragraph
To define the reader monad in Lean, the first step is to define the {anchorName Reader}`Reader` type and the effect that allows users to get ahold of the environment:

```anchor Reader
def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env
```
By convention, the Greek letter {anchorName Reader}`ρ`, which is pronounced “rho”, is used for environments.
:::

:::paragraph
The fact that constants in arithmetic expressions evaluate to constant functions suggests that the appropriate definition of {anchorName IdMonad}`pure` for {anchorName Reader}`Reader` is a a constant function:

```anchor ReaderPure
def Reader.pure (x : α) : Reader ρ α := fun _ => x
```
:::


On the other hand, {anchorName MonadContract}`bind` is a bit tricker.
Its type is {anchorTerm readerBindType}`Reader ρ α → (α → Reader ρ β) → Reader ρ β`.
This type can be easier to understand by unfolding the definition of {anchorName Reader}`Reader`, which yields {anchorTerm readerBindTypeEval}`(ρ → α) → (α → ρ → β) → (ρ → β)`.
It should take an environment-accepting function as its first argument, while the second argument should transform the result of the environment-accepting function into yet another environment-accepting function.
The result of combining these is itself a function, waiting for an environment.

It's possible to use Lean interactively to get help writing this function.
The first step is to write down the arguments and return type, being very explicit in order to get as much help as possible, with an underscore for the definition's body:
```anchor readerbind0
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  _
```
Lean provides a message that describes which variables are available in scope, and the type that's expected for the result.
The {lit}`⊢` symbol, called a {deftech}_turnstile_ due to its resemblance to subway entrances, separates the local variables from the desired type, which is {anchorTerm readerbind0}`ρ → β` in this message:
```anchorError readerbind0
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
⊢ ρ → β
```

Because the return type is a function, a good first step is to wrap a {kw}`fun` around the underscore:
```anchor readerbind1
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => _
```
The resulting message now shows the function's argument as a local variable:
```anchorError readerbind1
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ β
```

The only thing in the context that can produce a {anchorName readerbind2a}`β` is {anchorName readerbind2a}`next`, and it will require two arguments to do so.
Each argument can itself be an underscore:
```anchor readerbind2a
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next _ _
```
The two underscores have the following respective messages associated with them:
```anchorError readerbind2a
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ α
```
```anchorError readerbind2b
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ
```

:::paragraph
Attacking the first underscore, only one thing in the context can produce an {anchorName readerbind3}`α`, namely {anchorName readerbind3}`result`:
```anchor readerbind3
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result _) _
```
Now, both underscores have the same error message:
```anchorError readerbind3
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ
```
:::

:::paragraph
Happily, both underscores can be replaced by {anchorName readerbind4}`env`, yielding:

```anchor readerbind4
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env
```
:::

The final version can be obtained by undoing the unfolding of {anchorName Readerbind}`Reader` and cleaning up the explicit details:

```anchor Readerbind
def Reader.bind
    (result : Reader ρ α)
    (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env
```

It's not always possible to write correct functions by simply “following the types”, and it carries the risk of not understanding the resulting program.
However, it can also be easier to understand a program that has been written than one that has not, and the process of filling in the underscores can bring insights.
In this case, {anchorName Readerbind}`Reader.bind` works just like {anchorName IdMonad}`bind` for {anchorName IdMonad}`Id`, except it accepts an additional argument that it then passes down to its arguments, and this intuition can help in understanding how it works.

{anchorName ReaderPure}`Reader.pure` (which generates constant functions) and {anchorName Readerbind}`Reader.bind` obey the monad contract.
To check that {anchorTerm ReaderMonad1}`Reader.bind (Reader.pure v) f` is the same as {anchorTerm ReaderMonad1}`f v`, it's enough to replace definitions until the last step:
```anchorEvalSteps ReaderMonad1
Reader.bind (Reader.pure v) f
===>
fun env => f ((Reader.pure v) env) env
===>
fun env => f ((fun _ => v) env) env
===>
fun env => f v env
===>
f v
```
For every function {anchorName eta}`f`, {anchorTerm eta}`fun x => f x` is the same as {anchorName eta}`f`, so the first part of the contract is satisfied.
To check that {anchorTerm ReaderMonad2}`Reader.bind r Reader.pure` is the same as {anchorName ReaderMonad2}`r`, a similar technique works:
```anchorEvalSteps ReaderMonad2
Reader.bind r Reader.pure
===>
fun env => Reader.pure (r env) env
===>
fun env => (fun _ => (r env)) env
===>
fun env => r env
```
Because reader actions {anchorName ReaderMonad2}`r` are themselves functions, this is the same as {anchorName ReaderMonad2}`r`.
To check associativity, the same thing can be done for both {anchorEvalStep ReaderMonad3a 0}`Reader.bind (Reader.bind r f) g` and {anchorEvalStep ReaderMonad3b 0}`Reader.bind r (fun x => Reader.bind (f x) g)`:
```anchorEvalSteps ReaderMonad3a
Reader.bind (Reader.bind r f) g
===>
fun env => g ((Reader.bind r f) env) env
===>
fun env => g ((fun env' => f (r env') env') env) env
===>
fun env => g (f (r env) env) env
```

{anchorEvalStep ReaderMonad3b 0}`Reader.bind r (fun x => Reader.bind (f x) g)` reduces to the same expression:
```anchorEvalSteps ReaderMonad3b
Reader.bind r (fun x => Reader.bind (f x) g)
===>
Reader.bind r (fun x => fun env => g (f x env) env)
===>
fun env => (fun x => fun env' => g (f x env') env') (r env) env
===>
fun env => (fun env' => g (f (r env) env') env') env
===>
fun env => g (f (r env) env) env
```

Thus, a {anchorTerm MonadReaderInst}`Monad (Reader ρ)` instance is justified:

```anchor MonadReaderInst
instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env
```

The custom environments that will be passed to the expression evaluator can be represented as lists of pairs:

```anchor Env
abbrev Env : Type := List (String × (Int → Int → Int))
```
For instance, {anchorName exampleEnv}`exampleEnv` contains maximum and modulus functions:

```anchor exampleEnv
def exampleEnv : Env := [("max", max), ("mod", (· % ·))]
```

Lean already has a function {anchorName etc}`List.lookup` that finds the value associated with a key in a list of pairs, so {anchorName applyPrimReader}`applyPrimReader` needs only check whether the custom function is present in the environment. It returns {anchorTerm applyPrimReader}`0` if the function is unknown:

```anchor applyPrimReader
def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)
```

Using {anchorName readerEval}`evaluateM` with {anchorName readerEval}`applyPrimReader` and an expression results in a function that expects an environment.
Luckily, {anchorName readerEval}`exampleEnv` is available:
```anchor readerEval
open Expr Prim in
#eval
  evaluateM applyPrimReader
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv
```
```anchorInfo readerEval
9
```

Like {anchorName Many (module:=Examples.Monads.Many)}`Many`, {anchorName Reader}`Reader` is an example of an effect that is difficult to encode in most languages, but type classes and monads make it just as convenient as any other effect.
The dynamic or special variables found in Common Lisp, Clojure, and Emacs Lisp can be used like {anchorName Reader}`Reader`.
Similarly, Scheme and Racket's parameter objects are an effect that exactly correspond to {anchorName Reader}`Reader`.
The Kotlin idiom of context objects can solve a similar problem, but they are fundamentally a means of passing function arguments automatically, so this idiom is more like the encoding as a reader monad than it is an effect in the language.

## Exercises
%%%
tag := "monads-arithmetic-example-exercises"
%%%

### Checking Contracts
%%%
tag := none
%%%

Check the monad contract for {anchorTerm StateMonad}`State σ` and {anchorTerm MonadOptionExcept}`Except ε`.


### Readers with Failure
%%%
tag := none
%%%
Adapt the reader monad example so that it can also indicate failure when the custom operator is not defined, rather than just returning zero.
In other words, given these definitions:

```anchor ReaderFail
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α
```
do the following:
 1. Write suitable {lit}`pure` and {lit}`bind` functions
 2. Check that these functions satisfy the {anchorName evaluateM}`Monad` contract
 3. Write {anchorName evaluateM}`Monad` instances for {anchorName ReaderFail}`ReaderOption` and {anchorName ReaderFail}`ReaderExcept`
 4. Define suitable {anchorName evaluateM}`applyPrim` operators and test them with {anchorName evaluateM}`evaluateM` on some example expressions

### A Tracing Evaluator
%%%
tag := "monads-arithmetic-example-exercise-trace"
%%%

The {anchorName MonadWriter}`WithLog` type can be used with the evaluator to add optional tracing of some operations.
In particular, the type {anchorName ToTrace}`ToTrace` can serve as a signal to trace a given operator:

```anchor ToTrace
inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α
```
For the tracing evaluator, expressions should have type {anchorTerm ToTraceExpr}`Expr (Prim (ToTrace (Prim Empty)))`.
This says that the operators in the expression consist of addition, subtraction, and multiplication, augmented with traced versions of each. The innermost argument is {anchorName ToTraceExpr}`Empty` to signal that there are no further special operators inside of {anchorName ToTrace}`trace`, only the three basic ones.

Do the following:
 1. Implement a {anchorTerm MonadWriter}`Monad (WithLog logged)` instance
 2. Write an {anchorName applyTracedType}`applyTraced` function to apply traced operators to their arguments, logging both the operator and the arguments, with type {anchorTerm applyTracedType}`ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int`

If the exercise has been completed correctly, then
```anchor evalTraced
open Expr Prim ToTrace in
#eval
  evaluateM applyTraced
    (prim (other (trace times))
      (prim (other (trace plus)) (const 1)
        (const 2))
      (prim (other (trace minus)) (const 3)
        (const 4)))
```
should result in
```anchorInfo evalTraced
{ log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }
```

 Hint: values of type {anchorTerm ToTraceExpr}`Prim Empty` will appear in the resulting log. In order to display them as a result of {kw}`#eval`, the following instances are required:

```anchor ReprInstances
deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim
```
