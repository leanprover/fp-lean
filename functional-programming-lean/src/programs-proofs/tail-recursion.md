# Tail Recursion

While Lean's `do`-notation makes it possible to use traditional loop syntax such as `for` and `while`, these constructs are translated behind the scenes to invocations of recursive functions.
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

The function `NonTail.sum` adds the contents of a list of `Nat`s:
```lean
{{#example_decl Examples/ProgramsProofs/TCO.lean NonTailSum}}
```
Applying this function to the list `[1, 2, 3]` results in the following sequence of evaluation steps:
```lean
{{#example_eval Examples/ProgramsProofs/TCO.lean NonTailSumOneTwoThree}}
```
In the evaluation steps, parentheses indicate recursive calls to `NonTail.sum`.
In other words, to add the three numbers, the program must first check that the list is non-empty.
To add the head of the list (`1`) to the sum of the tail of the list, it is first necessary to compute the sum of the tail of the list:
```lean
{{#example_eval Examples/ProgramsProofs/TCO.lean NonTailSumOneTwoThree 1}}
```
But to compute the sum of the tail of the list, the program must check whether it is empty.
It is not - the tail is itself a list with `2` at its head.
The resulting step is waiting for the return of `NonTail.sum [3]`:
```lean
{{#example_eval Examples/ProgramsProofs/TCO.lean NonTailSumOneTwoThree 2}}
```
The whole point of the run-time call stack is to keep track of the values `1`, `2`, and `3` along with the instruction to add them to the result of the recursive call.
As recursive calls are completed, control returns to the stack frame that made the call, so each step of addition is performed.
Storing the heads of the list and the instructions to add them is not free; it takes space proportional to the length of the list.

The function `Tail.sum` also adds the contents of a list of `Nat`s:
```lean
{{#example_decl Examples/ProgramsProofs/TCO.lean TailSum}}
```
Applying it to the list `[1, 2, 3]` results in the following sequence of evaluation steps:
```lean
{{#example_eval Examples/ProgramsProofs/TCO.lean TailSumOneTwoThree}}
```
The internal helper function calls itself recursively, but it does so in a way where nothing needs to be remembered in order to compute the final result.
When `Tail.sumHelper` reaches its base case, control can be returned directly to `Tail.sum`, because the intermediate invocations of `Tail.sumHelper` simply return the results of their recursive calls unmodified.
In other words, a single stack frame can be re-used for each recursive invocation of `Tail.sumHelper`.
Tail-call elimination is exactly this re-use of the stack frame, and `Tail.sumHelper` is referred to as a _tail-recursive function_.

The first argument to `Tail.sumHelper` contains all of the information that would otherwise need to be tracked in the call stack—namely, the sum of the numbers encountered so far.
In each recursive call, this argument is updated with new information, rather than adding new information to the call stack.
Arguments like `soFar` that replace the information from the call stack are called _accumulators_.

At the time of writing and on the author's computer, `NonTail.sum` crashes with a stack overflow when passed a list with 216,856 or more entries.
`Tail.sum`, on the other hand, can sum a list of 100,000,000 elements without a stack overflow.
Because no new stack frames need to be pushed while running `Tail.sum`, it is completely equivalent to a `while` loop with a mutable variable that holds the current list.
At each recursive call, the function argument on the stack is simply replaced with the next node of the list.


## Tail and Non-Tail Positions

The reason why `Tail.sumHelper` is tail recursive is that the recursive call is in _tail position_.
Informally speaking, a function call is in tail position when the caller does not need to modify the returned value in any way, but will just return it directly.
More formally, tail position can be defined explicitly for expressions.

If a `match`-expression is in tail position, then each of its branches is also in tail position.
Once a `match` has selected a branch, control proceeds immediately to it.
Similarly, both branches of an `if`-expression are in tail position if the `if`-expression itself is in tail position.
Finally, if a `let`-expression is in tail position, then its body is as well.

All other positions are not in tail position.
The arguments to a function or a constructor are not in tail position because evaluation must track the function or constructor that will be applied to the argument's value.
The body of an inner function is not in tail position because control may not even pass to it: function bodies are not evaluated until the function is called.
Similarly, the body of a function type is not in tail position.
To evaluate `E` in `(x : α) → E`, it is necessary to track that the resulting type must have `(x : α) → ...` wrapped around it.

In `NonTail.sum`, the recursive call is not in tail position because it is an argument to `+`.
In `Tail.sumHelper`, the recursive call is in tail position because it is immediately underneath a pattern match, which itself is the body of the function.

At the time of writing, Lean only eliminates direct tail calls in recursive functions.
This means that tail calls to `f` in `f`'s definition will be eliminated, but not tail calls to some other function `g`.
While it is certainly possible to eliminate a tail call to some other function, saving a stack frame, this is not yet implemented in Lean.

## Reversing Lists

The function `NonTail.reverse` reverses lists by appending the head of each sub-list to the end of the result:
```lean
{{#example_decl Examples/ProgramsProofs/TCO.lean NonTailReverse}}
```
Using it to reverse `[1, 2, 3]` yields the following sequence of steps:
```lean
{{#example_eval Examples/ProgramsProofs/TCO.lean NonTailReverseSteps}}
```

The tail-recursive version uses `x :: ·` instead of `· ++ [x]` on the accumulator at each step:
```lean
{{#example_decl Examples/ProgramsProofs/TCO.lean TailReverse}}
```
This is because the context saved in each stack frame while computing with `NonTail.reverse` is applied beginning at the base case.
Each "remembered" piece of context is executed in last-in, first-out order.
On the other hand, the accumulator-passing version modifies the accumulator beginning from the first entry in the list, rather than the original base case, as can be seen in the series of reduction steps:
```lean
{{#example_eval Examples/ProgramsProofs/TCO.lean TailReverseSteps}}
```
In other words, the non-tail-recursive version starts at the base case, modifying the result of recursion from right to left through the list.
The entries in the list affect the accumulator in a first-in, first-out order.
The tail-recursive version with the accumulator starts at the head of the list, modifying an initial accumulator value from left to right through the list.

Because addition is commutative, nothing needed to be done to account for this in `Tail.sum`.
Appending lists is not commutative, so care must be taken to find an operation that has the same effect when run in the opposite direction.
Appending `[x]` after the result of the recursion in `NonTail.reverse` is analogous to adding `x` to the beginning of the list when the result is built in the opposite order.

## Multiple Recursive Calls

In the definition of `BinTree.mirror`, there are two recursive calls:
```lean
{{#example_decl Examples/Monads/Conveniences.lean mirrorNew}}
```
Just as imperative languages would typically use a while loop for functions like `reverse` and `sum`, they would typically use recursive functions for this kind of traversal.
This function cannot be straightforwardly rewritten to be tail recursive using accumulator-passing style.

Typically, if more than one recursive call is required for each recursive step, then it will be difficult to use accumulator-passing style.
This difficulty is similar to the difficulty of rewriting a recursive function to use a loop and an explicit data structure, with the added complication of convincing Lean that the function terminates.
However, as in `BinTree.mirror`, multiple recursive calls often indicate a data structure that has a constructor with multiple recursive occurrences of itself.
In these cases, the depth of the structure is often logarithmic with respect to its overall size, which makes the tradeoff between stack and heap less stark.
There are systematic techniques for making these functions tail-recursive, such as using _continuation-passing style_, but they are outside the scope of this chapter.

## Exercises

Translate each of the following non-tail-recursive functions into accumulator-passing tail-recursive functions:

```lean
{{#example_decl Examples/ProgramsProofs/TCO.lean NonTailLength}} 
```

```lean
{{#example_decl Examples/ProgramsProofs/TCO.lean NonTailFact}}
```

The translation of `NonTail.filter` should result in a program that takes constant stack space through tail recursion, and time linear in the length of the input list.
A constant factor overhead is acceptable relative to the original:
```lean
{{#example_decl Examples/ProgramsProofs/TCO.lean NonTailFilter}}
```
