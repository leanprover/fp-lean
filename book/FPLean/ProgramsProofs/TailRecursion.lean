import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.TCO"

#doc (Manual) "Tail Recursion" =>
%%%
tag := "tail-recursion"
%%%

While Lean's {kw}`do`-notation makes it possible to use traditional loop syntax such as {kw}`for` and {kw}`while`, these constructs are translated behind the scenes to invocations of recursive functions.
In most programming languages, recursive functions have a key disadvantage with respect to loops: loops consume no space on the stack, while recursive functions consume stack space proportional to the number of recursive calls.
Stack space is typically limited, and it is often necessary to take algorithms that are naturally expressed as recursive functions and rewrite them as loops paired with an explicit mutable heap-allocated stack.

In functional programming, the opposite is typically true.
Programs that are naturally expressed as mutable loops may consume stack space, while rewriting them to recursive functions can cause them to run quickly.
This is due to a key aspect of functional programming languages: _tail-call elimination_.
A tail call is a call from one function to another that can be compiled to an ordinary jump, replacing the current stack frame rather than pushing a new one, and tail-call elimination is the process of implementing this transformation.

Tail-call elimination is not just merely an optional optimization.
Its presence is a fundamental part of being able to write efficient functional code.
For it to be useful, it must be reliable.
Programmers must be able to reliably identify tail calls, and they must be able to trust that the compiler will eliminate them.

The function {anchorName NonTailSum}`NonTail.sum` adds the contents of a list of {anchorName NonTailSum}`Nat`s:

```anchor NonTailSum
def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
```
Applying this function to the list {anchorTerm NonTailSumOneTwoThree}`[1, 2, 3]` results in the following sequence of evaluation steps:
```anchorEvalSteps NonTailSumOneTwoThree
NonTail.sum [1, 2, 3]
===>
1 + (NonTail.sum [2, 3])
===>
1 + (2 + (NonTail.sum [3]))
===>
1 + (2 + (3 + (NonTail.sum [])))
===>
1 + (2 + (3 + 0))
===>
1 + (2 + 3)
===>
1 + 5
===>
6
```
In the evaluation steps, parentheses indicate recursive calls to {anchorName NonTailSumOneTwoThree}`NonTail.sum`.
In other words, to add the three numbers, the program must first check that the list is non-empty.
To add the head of the list ({anchorTerm NonTailSumOneTwoThree}`1`) to the sum of the tail of the list, it is first necessary to compute the sum of the tail of the list:
```anchorEvalStep NonTailSumOneTwoThree 1
1 + (NonTail.sum [2, 3])
```
But to compute the sum of the tail of the list, the program must check whether it is empty.
It is not—the tail is itself a list with {anchorTerm NonTailSumOneTwoThree}`2` at its head.
The resulting step is waiting for the return of {anchorTerm NonTailSumOneTwoThree}`NonTail.sum [3]`:
```anchorEvalStep NonTailSumOneTwoThree 2
1 + (2 + (NonTail.sum [3]))
```
The whole point of the run-time call stack is to keep track of the values {anchorTerm NonTailSumOneTwoThree}`1`, {anchorTerm NonTailSumOneTwoThree}`2`, and {anchorTerm NonTailSumOneTwoThree}`3` along with the instruction to add them to the result of the recursive call.
As recursive calls are completed, control returns to the stack frame that made the call, so each step of addition is performed.
Storing the heads of the list and the instructions to add them is not free; it takes space proportional to the length of the list.

The function {anchorName TailSum}`Tail.sum` also adds the contents of a list of {anchorName TailSum}`Nat`s:

```anchor TailSum
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs
```
Applying it to the list {anchorTerm TailSumOneTwoThree}`[1, 2, 3]` results in the following sequence of evaluation steps:
```anchorEvalSteps TailSumOneTwoThree
Tail.sum [1, 2, 3]
===>
Tail.sumHelper 0 [1, 2, 3]
===>
Tail.sumHelper (0 + 1) [2, 3]
===>
Tail.sumHelper 1 [2, 3]
===>
Tail.sumHelper (1 + 2) [3]
===>
Tail.sumHelper 3 [3]
===>
Tail.sumHelper (3 + 3) []
===>
Tail.sumHelper 6 []
===>
6
```
The internal helper function calls itself recursively, but it does so in a way where nothing needs to be remembered in order to compute the final result.
When {anchorName TailSum}`Tail.sumHelper` reaches its base case, control can be returned directly to {anchorName TailSum}`Tail.sum`, because the intermediate invocations of {anchorName TailSum}`Tail.sumHelper` simply return the results of their recursive calls unmodified.
In other words, a single stack frame can be re-used for each recursive invocation of {anchorName TailSum}`Tail.sumHelper`.
Tail-call elimination is exactly this re-use of the stack frame, and {anchorName TailSum}`Tail.sumHelper` is referred to as a _tail-recursive function_.

The first argument to {anchorName TailSum}`Tail.sumHelper` contains all of the information that would otherwise need to be tracked in the call stack—namely, the sum of the numbers encountered so far.
In each recursive call, this argument is updated with new information, rather than adding new information to the call stack.
Arguments like {anchorName TailSum}`soFar` that replace the information from the call stack are called _accumulators_.

At the time of writing and on the author's computer, {anchorName NonTailSum}`NonTail.sum` crashes with a stack overflow when passed a list with 216,856 or more entries.
{anchorName TailSum}`Tail.sum`, on the other hand, can sum a list of 100,000,000 elements without a stack overflow.
Because no new stack frames need to be pushed while running {anchorName TailSum}`Tail.sum`, it is completely equivalent to a {kw}`while` loop with a mutable variable that holds the current list.
At each recursive call, the function argument on the stack is simply replaced with the next node of the list.


# Tail and Non-Tail Positions
%%%
tag := "tail-positions"
%%%

The reason why {anchorName TailSum}`Tail.sumHelper` is tail recursive is that the recursive call is in _tail position_.
Informally speaking, a function call is in tail position when the caller does not need to modify the returned value in any way, but will just return it directly.
More formally, tail position can be defined explicitly for expressions.

If a {kw}`match`-expression is in tail position, then each of its branches is also in tail position.
Once a {kw}`match` has selected a branch, control proceeds immediately to it.
Similarly, both branches of an {kw}`if`-expression are in tail position if the {kw}`if`-expression itself is in tail position.
Finally, if a {kw}`let`-expression is in tail position, then its body is as well.

All other positions are not in tail position.
The arguments to a function or a constructor are not in tail position because evaluation must track the function or constructor that will be applied to the argument's value.
The body of an inner function is not in tail position because control may not even pass to it: function bodies are not evaluated until the function is called.
Similarly, the body of a function type is not in tail position.
To evaluate {lit}`E` in {lit}`(x : α) → E`, it is necessary to track that the resulting type must have {lit}`(x : α) → ...` wrapped around it.

In {anchorName NonTailSum}`NonTail.sum`, the recursive call is not in tail position because it is an argument to {anchorTerm NonTailSum}`+`.
In {anchorName TailSum}`Tail.sumHelper`, the recursive call is in tail position because it is immediately underneath a pattern match, which itself is the body of the function.

At the time of writing, Lean only eliminates direct tail calls in recursive functions.
This means that tail calls to {lit}`f` in {lit}`f`'s definition will be eliminated, but not tail calls to some other function {lit}`g`.
While it is certainly possible to eliminate a tail call to some other function, saving a stack frame, this is not yet implemented in Lean.

# Reversing Lists
%%%
tag := "reversing-lists-tail-recursively"
%%%

The function {anchorName NonTailReverse}`NonTail.reverse` reverses lists by appending the head of each sub-list to the end of the result:

```anchor NonTailReverse
def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]
```
Using it to reverse {anchorTerm NonTailReverseSteps}`[1, 2, 3]` yields the following sequence of steps:
```anchorEvalSteps NonTailReverseSteps
NonTail.reverse [1, 2, 3]
===>
(NonTail.reverse [2, 3]) ++ [1]
===>
((NonTail.reverse [3]) ++ [2]) ++ [1]
===>
(((NonTail.reverse []) ++ [3]) ++ [2]) ++ [1]
===>
(([] ++ [3]) ++ [2]) ++ [1]
===>
([3] ++ [2]) ++ [1]
===>
[3, 2] ++ [1]
===>
[3, 2, 1]
```

The tail-recursive version uses {lit}`x :: ·` instead of {lit}`· ++ [x]` on the accumulator at each step:

```anchor TailReverse
def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs
```
This is because the context saved in each stack frame while computing with {anchorName NonTailReverse}`NonTail.reverse` is applied beginning at the base case.
Each “remembered” piece of context is executed in last-in, first-out order.
On the other hand, the accumulator-passing version modifies the accumulator beginning from the first entry in the list, rather than the original base case, as can be seen in the series of reduction steps:
```anchorEvalSteps TailReverseSteps
Tail.reverse [1, 2, 3]
===>
Tail.reverseHelper [] [1, 2, 3]
===>
Tail.reverseHelper [1] [2, 3]
===>
Tail.reverseHelper [2, 1] [3]
===>
Tail.reverseHelper [3, 2, 1] []
===>
[3, 2, 1]
```
In other words, the non-tail-recursive version starts at the base case, modifying the result of recursion from right to left through the list.
The entries in the list affect the accumulator in a first-in, first-out order.
The tail-recursive version with the accumulator starts at the head of the list, modifying an initial accumulator value from left to right through the list.

Because addition is commutative, nothing needed to be done to account for this in {anchorName TailSum}`Tail.sum`.
Appending lists is not commutative, so care must be taken to find an operation that has the same effect when run in the opposite direction.
Appending {anchorTerm NonTailReverse}`[x]` after the result of the recursion in {anchorName NonTailReverse}`NonTail.reverse` is analogous to adding {anchorName NonTailReverse}`x` to the beginning of the list when the result is built in the opposite order.

# Multiple Recursive Calls
%%%
tag := "multiple-call-tail-recursion"
%%%

In the definition of {anchorName mirrorNew (module := Examples.Monads.Conveniences)}`BinTree.mirror`, there are two recursive calls:

```anchor mirrorNew (module := Examples.Monads.Conveniences)
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
```
Just as imperative languages would typically use a while loop for functions like {anchorName NonTailReverse}`reverse` and {anchorName NonTailSum}`sum`, they would typically use recursive functions for this kind of traversal.
This function cannot be straightforwardly rewritten to be tail recursive using accumulator-passing style, at least not using the techniques presented in this book.

Typically, if more than one recursive call is required for each recursive step, then it will be difficult to use accumulator-passing style.
This difficulty is similar to the difficulty of rewriting a recursive function to use a loop and an explicit data structure, with the added complication of convincing Lean that the function terminates.
However, as in {anchorName mirrorNew (module:=Examples.Monads.Conveniences)}`BinTree.mirror`, multiple recursive calls often indicate a data structure that has a constructor with multiple recursive occurrences of itself.
In these cases, the depth of the structure is often logarithmic with respect to its overall size, which makes the tradeoff between stack and heap less stark.
There are systematic techniques for making these functions tail-recursive, such as using _continuation-passing style_ and _defunctionalization_, but they are outside the scope of this book.

# Exercises
%%%
tag := "tail-recursion-exercises"
%%%

Translate each of the following non-tail-recursive functions into accumulator-passing tail-recursive functions:


```anchor NonTailLength
def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1
```


```anchor NonTailFact
def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)
```

The translation of {anchorName NonTailFilter}`NonTail.filter` should result in a program that takes constant stack space through tail recursion, and time linear in the length of the input list.
A constant factor overhead is acceptable relative to the original:

```anchor NonTailFilter
def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs
```
