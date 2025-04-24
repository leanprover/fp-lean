## Example: Arithmetic in Monads

Monads are a way of encoding programs with side effects into a language that does not have them.
It would be easy to read this as a sort of admission that pure functional programs are missing something important, requiring programmers to jump through hoops just to write a normal program.
However, while using the `Monad` API does impose a syntactic cost on a program, it brings two important benefits:
 1. Programs must be honest about which effects they use in their types. A quick glance at a type signature describes _everything_ that the program can do, rather than just what it accepts and what it returns.
 2. Not every language provides the same effects. For example, only some languages have exceptions. Other languages have unique, exotic effects, such as [Icon's searching over multiple values](https://www2.cs.arizona.edu/icon/) and Scheme or Ruby's continuations. Because monads can encode _any_ effect, programmers can choose which ones are the best fit for a given application, rather than being stuck with what the language developers provided.

One example of a program that can make sense in a variety of monads is an evaluator for arithmetic expressions.

### Arithmetic Expressions

An arithmetic expression is either a literal integer or a primitive binary operator applied to two expressions. The operators are addition, subtraction, multiplication, and division:
```lean
{{#example_decl Examples/Monads/Class.lean ExprArith}}
```
The expression `2 + 3` is represented:
```lean
{{#example_decl Examples/Monads/Class.lean twoPlusThree}}
```
and `14 / (45 - 5 * 9)` is represented:
```lean
{{#example_decl Examples/Monads/Class.lean exampleArithExpr}}
```

### Evaluating Expressions

Because expressions include division, and division by zero is undefined, evaluation might fail.
One way to represent failure is to use `Option`:
```lean
{{#example_decl Examples/Monads/Class.lean evaluateOptionCommingled}}
```
This definition uses the `Monad Option` instance to propagate failures from evaluating both branches of a binary operator.
However, the function mixes two concerns: evaluating subexpressions and applying a binary operator to the results.
It can be improved by splitting it into two functions:
```lean
{{#example_decl Examples/Monads/Class.lean evaluateOptionSplit}}
```

Running `{{#example_in Examples/Monads/Class.lean fourteenDivOption}}` yields `{{#example_out Examples/Monads/Class.lean fourteenDivOption}}`, as expected, but this is not a very useful error message.
Because the code was written using `>>=` rather than by explicitly handling the `none` constructor, only a small modification is required for it to provide an error message on failure:
```lean
{{#example_decl Examples/Monads/Class.lean evaluateExcept}}
```
The only difference is that the type signature mentions `Except String` instead of `Option`, and the failing case uses `Except.error` instead of `none`.
By making `evaluate` polymorphic over its monad and passing it `applyPrim` as an argument, a single evaluator becomes capable of both forms of error reporting:
```lean
{{#example_decl Examples/Monads/Class.lean evaluateM}}
```
Using it with `applyPrimOption` works just like the first version of `evaluate`:
```lean
{{#example_in Examples/Monads/Class.lean evaluateMOption}}
```
```output info
{{#example_out Examples/Monads/Class.lean evaluateMOption}}
```
Similarly, using it with `applyPrimExcept` works just like the version with error messages:
```lean
{{#example_in Examples/Monads/Class.lean evaluateMExcept}}
```
```output info
{{#example_out Examples/Monads/Class.lean evaluateMExcept}}
```

The code can still be improved.
The functions `applyPrimOption` and `applyPrimExcept` differ only in their treatment of division, which can be extracted into another parameter to the evaluator:
```lean
{{#example_decl Examples/Monads/Class.lean evaluateMRefactored}}
```

In this refactored code, the fact that the two code paths differ only in their treatment of failure has been made fully apparent.

### Further Effects

Failure and exceptions are not the only kinds of effects that can be interesting when working with an evaluator.
While division's only side effect is failure, adding other primitive operators to the expressions make it possible to express other effects.

The first step is an additional refactoring, extracting division from the datatype of primitives:
```lean
{{#example_decl Examples/Monads/Class.lean PrimCanFail}}
```
The name `CanFail` suggests that the effect introduced by division is potential failure.

The second step is to broaden the scope of the division handler argument to `evaluateM` so that it can process any special operator:
```lean
{{#example_decl Examples/Monads/Class.lean evaluateMMorePoly}}
```

#### No Effects

The type `Empty` has no constructors, and thus no values, like the `Nothing` type in Scala or Kotlin.
In Scala and Kotlin, `Nothing` can represent computations that never return a result, such as functions that crash the program, throw exceptions, or always fall into infinite loops.
An argument to a function or method of type `Nothing` indicates dead code, as there will never be a suitable argument value.
Lean doesn't support infinite loops and exceptions, but `Empty` is still useful as an indication to the type system that a function cannot be called.
Using the syntax `nomatch E` when `E` is an expression whose type has no constructors indicates to Lean that the current expression need not return a result, because it could never have been called. 

Using `Empty` as the parameter to `Prim` indicates that there are no additional cases beyond `Prim.plus`, `Prim.minus`, and `Prim.times`, because it is impossible to come up with a value of type `Empty` to place in the `Prim.other` constructor.
Because a function to apply an operator of type `Empty` to two integers can never be called, it doesn't need to return a result.
Thus, it can be used in _any_ monad:
```lean
{{#example_decl Examples/Monads/Class.lean applyEmpty}}
```
This can be used together with `Id`, the identity monad, to evaluate expressions that have no effects whatsoever:
```lean
{{#example_in Examples/Monads/Class.lean evalId}}
```
```output info
{{#example_out Examples/Monads/Class.lean evalId}}
```

#### Nondeterministic Search

Instead of simply failing when encountering division by zero, it would also be sensible to backtrack and try a different input.
Given the right monad, the very same `evaluateM` can perform a nondeterministic search for a _set_ of answers that do not result in failure.
This requires, in addition to division, some means of specifying a choice of results.
One way to do this is to add a function `choose` to the language of expressions that instructs the evaluator to pick either of its arguments while searching for non-failing results.

The result of the evaluator is now a multiset of values, rather than a single value.
The rules for evaluation into a multiset are:
 * Constants \\( n \\) evaluate to singleton sets \\( \{n\} \\).
 * Arithmetic operators other than division are called on each pair from the Cartesian product of the operators, so \\( X + Y \\) evaluates to \\( \\{ x + y \\mid x ∈ X, y ∈ Y \\} \\).
 * Division \\( X / Y \\) evaluates to \\( \\{ x / y \\mid x ∈ X, y ∈ Y, y ≠ 0\\} \\). In other words, all \\( 0 \\) values in \\( Y \\)  are thrown out.
 * A choice \\( \\mathrm{choose}(x, y) \\) evaluates to \\( \\{ x, y \\} \\).

For example, \\( 1 + \\mathrm{choose}(2, 5) \\) evaluates to \\( \\{ 3, 6 \\} \\), \\(1 + 2 / 0 \\) evaluates to \\( \\{\\} \\), and \\( 90 / (\\mathrm{choose}(-5, 5) + 5) \\) evaluates to \\( \\{ 9 \\} \\).
Using multisets instead of true sets simplifies the code by removing the need to check for uniqueness of elements.

A monad that represents this non-deterministic effect must be able to represent a situation in which there are no answers, and a situation in which there is at least one answer together with any remaining answers:
```lean
{{#example_decl Examples/Monads/Many.lean Many}}
```
This datatype looks very much like `List`.
The difference is that where `cons` stores the rest of the list, `more` stores a function that should compute the next value on demand.
This means that a consumer of `Many` can stop the search when some number of results have been found.

A single result is represented by a `more` constructor that returns no further results:
```lean
{{#example_decl Examples/Monads/Many.lean one}}
```
The union of two multisets of results can be computed by checking whether the first multiset is empty.
If so, the second multiset is the union.
If not, the union consists of the first element of the first multiset followed by the union of the rest of the first multiset with the second multiset:
```lean
{{#example_decl Examples/Monads/Many.lean union}}
```

It can be convenient to start a search process with a list of values.
`Many.fromList` converts a list into a multiset of results:
```lean
{{#example_decl Examples/Monads/Many.lean fromList}}
```
Similarly, once a search has been specified, it can be convenient to extract either a number of values, or all the values:
```lean
{{#example_decl Examples/Monads/Many.lean take}}
```

A `Monad Many` instance requires a `bind` operator.
In a nondeterministic search, sequencing two operations consists of taking all possibilities from the first step and running the rest of the program on each of them, taking the union of the results.
In other words, if the first step returns three possible answers, the second step needs to be tried for all three.
Because the second step can return any number of answers for each input, taking their union represents the entire search space.
```lean
{{#example_decl Examples/Monads/Many.lean bind}}
```

`Many.one` and `Many.bind` obey the monad contract.
To check that `Many.bind (Many.one v) f` is the same as `f v`, start by evaluating the expression as far as possible:
```lean
{{#example_eval Examples/Monads/Many.lean bindLeft}}
```
The empty multiset is a right identity of `union`, so the answer is equivalent to `f v`.
To check that `Many.bind v Many.one` is the same as `v`, consider that `bind` takes the union of applying `Many.one` to each element of `v`.
In other words, if `v` has the form `{v1, v2, v3, ..., vn}`, then `Many.bind v Many.one` is `{v1} ∪ {v2} ∪ {v3} ∪ ... ∪ {vn}`, which is `{v1, v2, v3, ..., vn}`.

Finally, to check that `Many.bind` is associative, check that `Many.bind (Many.bind bind v f) g` is the same as `Many.bind v (fun x => Many.bind (f x) g)`.
If `v` has the form `{v1, v2, v3, ..., vn}`, then:
```lean
Many.bind v f
===>
f v1 ∪ f v2 ∪ f v3 ∪ ... ∪ f vn
```
which means that
```lean
Many.bind (Many.bind bind v f) g
===>
Many.bind (f v1) g ∪
Many.bind (f v2) g ∪
Many.bind (f v3) g ∪
... ∪
Many.bind (f vn) g
```
Similarly,
```lean
Many.bind v (fun x => Many.bind (f x) g)
===>
(fun x => Many.bind (f x) g) v1 ∪
(fun x => Many.bind (f x) g) v2 ∪
(fun x => Many.bind (f x) g) v3 ∪
... ∪
(fun x => Many.bind (f x) g) vn
===>
Many.bind (f v1) g ∪
Many.bind (f v2) g ∪
Many.bind (f v3) g ∪
... ∪
Many.bind (f vn) g
```
Thus, both sides are equal, so `Many.bind` is associative.

The resulting monad instance is:
```lean
{{#example_decl Examples/Monads/Many.lean MonadMany}}
```
An example search using this monad finds all the combinations of numbers in a list that add to 15:
```lean
{{#example_decl Examples/Monads/Many.lean addsTo}}
```
The search process is recursive over the list.
The empty list is a successful search when the goal is `0`; otherwise, it fails.
When the list is non-empty, there are two possibilities: either the head of the list is greater than the goal, in which case it cannot participate in any successful searches, or it is not, in which case it can.
If the head of the list is _not_ a candidate, then the search proceeds to the tail of the list.
If the head is a candidate, then there are two possibilities to be combined with `Many.union`: either the solutions found contain the head, or they do not.
The solutions that do not contain the head are found with a recursive call on the tail, while the solutions that do contain it result from subtracting the head from the goal, and then attaching the head to the solutions that result from the recursive call.

The helper `printList` ensures that one result is displayed per line:
```lean
{{#example_decl Examples/Monads/Many.lean printList}}

{{#example_in Examples/Monads/Many.lean addsToFifteen}}
```
```output info
{{#example_out Examples/Monads/Many.lean addsToFifteen}}
```


Returning to the arithmetic evaluator that produces multisets of results, the `both` and `neither` operators can be written as follows:
```lean
{{#example_decl Examples/Monads/Class.lean NeedsSearch}}
```
Using these operators, the earlier examples can be evaluated:
```lean
{{#example_decl Examples/Monads/Class.lean opening}}

{{#example_in Examples/Monads/Class.lean searchA}}
```
```output info
{{#example_out Examples/Monads/Class.lean searchA}}
```
```lean
{{#example_in Examples/Monads/Class.lean searchB}}
```
```output info
{{#example_out Examples/Monads/Class.lean searchB}}
```
```lean
{{#example_in Examples/Monads/Class.lean searchC}}
```
```output info
{{#example_out Examples/Monads/Class.lean searchC}}
```

#### Custom Environments

The evaluator can be made user-extensible by allowing strings to be used as operators, and then providing a mapping from strings to a function that implements them.
For example, users could extend the evaluator with a remainder operator or with one that returns the maximum of its two arguments.
The mapping from function names to function implementations is called an _environment_.

The environments needs to be passed in each recursive call.
Initially, it might seem that `evaluateM` needs an extra argument to hold the environment, and that this argument should be passed to each recursive invocation.
However, passing an argument like this is another form of monad, so an appropriate `Monad` instance allows the evaluator to be used unchanged.

Using functions as a monad is typically called a _reader_ monad.
When evaluating expressions in the reader monad, the following rules are used:
 * Constants \\( n \\) evaluate to constant functions \\( λ e . n \\),
 * Arithmetic operators evaluate to functions that pass their arguments on, so \\( f + g \\) evaluates to \\( λ e . f(e) + g(e) \\), and
 * Custom operators evaluate to the result of applying the custom operator to the arguments, so \\( f \\ \\mathrm{OP}\\ g \\) evaluates to
   \\[
     λ e .
     \\begin{cases}
     h(f(e), g(e)) & \\mathrm{if}\\ e\\ \\mathrm{contains}\\ (\\mathrm{OP}, h) \\\\
     0 & \\mathrm{otherwise}
     \\end{cases}
   \\]
   with \\( 0 \\) serving as a fallback in case an unknown operator is applied.

To define the reader monad in Lean, the first step is to define the `Reader` type and the effect that allows users to get ahold of the environment:
```lean
{{#example_decl Examples/Monads/Class.lean Reader}}
```
By convention, the Greek letter `ρ`, which is pronounced "rho", is used for environments.

The fact that constants in arithmetic expressions evaluate to constant functions suggests that the appropriate definition of `pure` for `Reader` is a a constant function:
```lean
{{#example_decl Examples/Monads/Class.lean ReaderPure}}
```

On the other hand, `bind` is a bit tricker.
Its type is `{{#example_out Examples/Monads/Class.lean readerBindType}}`.
This type can be easier to understand by unfolding the definition of `Reader`, which yields `{{#example_out Examples/Monads/Class.lean readerBindTypeEval}}`.
It should take an environment-accepting function as its first argument, while the second argument should transform the result of the environment-accepting function into yet another environment-accepting function.
The result of combining these is itself a function, waiting for an environment.

It's possible to use Lean interactively to get help writing this function.
The first step is to write down the arguments and return type, being very explicit in order to get as much help as possible, with an underscore for the definition's body:
```lean
{{#example_in Examples/Monads/Class.lean readerbind0}}
```
Lean provides a message that describes which variables are available in scope, and the type that's expected for the result.
The `⊢` symbol, called a _turnstile_ due to its resemblance to subway entrances, separates the local variables from the desired type, which is `ρ → β` in this message:
```output error
{{#example_out Examples/Monads/Class.lean readerbind0}}
```

Because the return type is a function, a good first step is to wrap a `fun` around the underscore:
```lean
{{#example_in Examples/Monads/Class.lean readerbind1}}
```
The resulting message now shows the function's argument as a local variable:
```output error
{{#example_out Examples/Monads/Class.lean readerbind1}}
```

The only thing in the context that can produce a `β` is `next`, and it will require two arguments to do so.
Each argument can itself be an underscore:
```lean
{{#example_in Examples/Monads/Class.lean readerbind2a}}
```
The two underscores have the following respective messages associated with them:
```output error
{{#example_out Examples/Monads/Class.lean readerbind2a}}
```
```output error
{{#example_out Examples/Monads/Class.lean readerbind2b}}
```

Attacking the first underscore, only one thing in the context can produce an `α`, namely `result`:
```lean
{{#example_in Examples/Monads/Class.lean readerbind3}}
```
Now, both underscores have the same error message:
```output error
{{#example_out Examples/Monads/Class.lean readerbind3}}
```
Happily, both underscores can be replaced by `env`, yielding:
```lean
{{#example_decl Examples/Monads/Class.lean readerbind4}}
```

The final version can be obtained by undoing the unfolding of `Reader` and cleaning up the explicit details:
```lean
{{#example_decl Examples/Monads/Class.lean Readerbind}}
```

It's not always possible to write correct functions by simply "following the types", and it carries the risk of not understanding the resulting program.
However, it can also be easier to understand a program that has been written than one that has not, and the process of filling in the underscores can bring insights.
In this case, `Reader.bind` works just like `bind` for `Id`, except it accepts an additional argument that it then passes down to its arguments, and this intuition can help in understanding how it works.

`Reader.pure`, which generates constant functions, and `Reader.bind` obey the monad contract.
To check that `Reader.bind (Reader.pure v) f` is the same as `f v`, it's enough to replace definitions until the last step:
```lean
{{#example_eval Examples/Monads/Class.lean ReaderMonad1}}
```
For every function `f`, `fun x => f x` is the same as `f`, so the first part of the contract is satisfied.
To check that `Reader.bind r Reader.pure` is the same as `r`, a similar technique works:
```lean
{{#example_eval Examples/Monads/Class.lean ReaderMonad2}}
```
Because reader actions `r` are themselves functions, this is the same as `r`.
To check associativity, the same thing can be done for both `{{#example_eval Examples/Monads/Class.lean ReaderMonad3a 0}}` and `{{#example_eval Examples/Monads/Class.lean ReaderMonad3b 0}}`:
```lean
{{#example_eval Examples/Monads/Class.lean ReaderMonad3a}}
```

```lean
{{#example_eval Examples/Monads/Class.lean ReaderMonad3b}}
```

Thus, a `Monad (Reader ρ)` instance is justified:
```lean
{{#example_decl Examples/Monads/Class.lean MonadReaderInst}}
```

The custom environments that will be passed to the expression evaluator can be represented as lists of pairs:
```lean
{{#example_decl Examples/Monads/Class.lean Env}}
```
For instance, `exampleEnv` contains maximum and modulus functions:
```lean
{{#example_decl Examples/Monads/Class.lean exampleEnv}}
```

Lean already has a function `List.lookup` that finds the value associated with a key in a list of pairs, so `applyPrimReader` needs only check whether the custom function is present in the environment. It returns `0` if the function is unknown:
```lean
{{#example_decl Examples/Monads/Class.lean applyPrimReader}}
```

Using `evaluateM` with `applyPrimReader` and an expression results in a function that expects an environment.
Luckily, `exampleEnv` is available:
```lean
{{#example_in Examples/Monads/Class.lean readerEval}}
```
```output info
{{#example_out Examples/Monads/Class.lean readerEval}}
```

Like `Many`, `Reader` is an example of an effect that is difficult to encode in most languages, but type classes and monads make it just as convenient as any other effect.
The dynamic or special variables found in Common Lisp, Clojure, and Emacs Lisp can be used like `Reader`.
Similarly, Scheme and Racket's parameter objects are an effect that exactly correspond to `Reader`.
The Kotlin idiom of context objects can solve a similar problem, but they are fundamentally a means of passing function arguments automatically, so this idiom is more like the encoding as a reader monad than it is an effect in the language.

## Exercises

### Checking Contracts

Check the monad contract for `State σ` and `Except ε`.


### Readers with Failure
Adapt the reader monad example so that it can also indicate failure when the custom operator is not defined, rather than just returning zero.
In other words, given these definitions:
```lean
{{#example_decl Examples/Monads/Class.lean ReaderFail}}
```
do the following:
 1. Write suitable `pure` and `bind` functions
 2. Check that these functions satisfy the `Monad` contract
 3. Write `Monad` instances for `ReaderOption` and `ReaderExcept`
 4. Define suitable `applyPrim` operators and test them with `evaluateM` on some example expressions

### A Tracing Evaluator

The `WithLog` type can be used with the evaluator to add optional tracing of some operations.
In particular, the type `ToTrace` can serve as a signal to trace a given operator:
```lean
{{#example_decl Examples/Monads/Class.lean ToTrace}}
```
For the tracing evaluator, expressions should have type `Expr (Prim (ToTrace (Prim Empty)))`.
This says that the operators in the expression consist of addition, subtraction, and multiplication, augmented with traced versions of each. The innermost argument is `Empty` to signal that there are no further special operators inside of `trace`, only the three basic ones.

Do the following:
 1. Implement a `Monad (WithLog logged)` instance
 2. Write an `{{#example_in Examples/Monads/Class.lean applyTracedType}}` function to apply traced operators to their arguments, logging both the operator and the arguments, with type `{{#example_out Examples/Monads/Class.lean applyTracedType}}`
 
If the exercise has been completed correctly, then
```lean
{{#example_in Examples/Monads/Class.lean evalTraced}}
```
should result in
```output info
{{#example_out Examples/Monads/Class.lean evalTraced}}
```
 
 Hint: values of type `Prim Empty` will appear in the resulting log. In order to display them as a result of `#eval`, the following instances are required:
 ```lean
 {{#example_decl Examples/Monads/Class.lean ReprInstances}}
 ```
