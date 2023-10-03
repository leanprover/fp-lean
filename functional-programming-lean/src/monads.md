# Monads

In C# and Kotlin, the `?.` operator is a way to look up a property or call a method on a potentially-null value.
If the receiver is `null`, the whole expression is null.
Otherwise, the underlying non-`null` value receives the call.
Uses of `?.` can be chained, in which case the first `null` result terminates the chain of lookups.
Chaining null-checks like this is much more convenient than writing and maintaining deeply nested `if`s.

Similarly, exceptions are significantly more convenient than manually checking and propagating error codes.
At the same time, logging is easiest to accomplish by having a dedicated logging framework, rather than having each function return both its log results and its return value.
Chained null checks and exceptions typically require language designers to anticipate this use case, while logging frameworks typically make use of side effects to decouple code that logs from the accumulation of the logs.

All these features and more can be implemented in library code as instances of a common API called `Monad`.
Lean provides dedicated syntax that makes this API convenient to use, but can also get in the way of understanding what is going on behind the scenes.
This chapter begins with the nitty-gritty presentation of manually nesting null checks, and builds from there to the convenient, general API.
Please suspend your disbelief in the meantime.

## Checking for `none`: Don't Repeat Yourself

In Lean, pattern matching can be used to chain checks for null.
Getting the first entry from a list can just use the optional indexing notation:
```lean
{{#example_decl Examples/Monads.lean first}}
```
The result must be an `Option` because empty lists have no first entry.
Extracting the first and third entries requires a check that each is not `none`:
```lean
{{#example_decl Examples/Monads.lean firstThird}}
```
Similarly, extracting the first, third, and fifth entries requires more checks that the values are not `none`:
```lean
{{#example_decl Examples/Monads.lean firstThirdFifth}}
```
And adding the seventh entry to this sequence begins to become quite unmanageable:
```lean
{{#example_decl Examples/Monads.lean firstThirdFifthSeventh}}
```


The fundamental problem with this code is that it addresses two concerns: extracting the numbers and checking that all of them are present, but the second concern is addressed by copying and pasting the code that handles the `none` case.
It is often good style to lift a repetitive segment into a helper function:
```lean
{{#example_decl Examples/Monads.lean andThenOption}}
```
This helper, which is used similarly to `?.` in C# and Kotlin, takes care of propagating `none` values.
It takes two arguments: an optional value and a function to apply when the value is not `none`.
If the first argument is `none`, then the helper returns `none`.
If the first argument is not `none`, then the function is applied to the contents of the `some` constructor.

Now, `firstThird` can be rewritten to use `andThen` instead of pattern matching:
```lean
{{#example_decl Examples/Monads.lean firstThirdandThen}}
```
In Lean, functions don't need to be enclosed in parentheses when passed as arguments.
The following equivalent definition uses more parentheses and indents the bodies of functions:
```lean
{{#example_decl Examples/Monads.lean firstThirdandThenExpl}}
```
The `andThen` helper provides a sort of "pipeline" through which values flow, and the version with the somewhat unusual indentation is more suggestive of this fact.
Improving the syntax used to write `andThen` can make these computations even easier to understand.

### Infix Operators

In Lean, infix operators can be declared using the `infix`, `infixl`, and `infixr` commands, which create (respectively) non-associative, left-associative, and right-associative operators.
When used multiple times in a row, a _left associative_ operator stacks up the opening parentheses on the left side of the expression.
The addition operator `+` is left associative, so `{{#example_in Examples/Monads.lean plusFixity}}` is equivalent to `{{#example_out Examples/Monads.lean plusFixity}}`.
The exponentiation operator `^` is right associative, so `{{#example_in Examples/Monads.lean powFixity}}` is equivalent to `{{#example_out Examples/Monads.lean powFixity}}`.
Comparison operators such as `<` are non-associative, so `x < y < z` is a syntax error and requires manual parentheses.

The following declaration makes `andThen` into an infix operator:
```lean
{{#example_decl Examples/Monads.lean andThenOptArr}}
```
The number following the colon declares the _precedence_ of the new infix operator.
In ordinary mathematical notation, `{{#example_in Examples/Monads.lean plusTimesPrec}}` is equivalent to `{{#example_out Examples/Monads.lean plusTimesPrec}}` even though both `+` and `*` are left associative.
In Lean, `+` has precedence 65 and `*` has precedence 70.
Higher-precedence operators are applied before lower-precedence operators.
According to the declaration of `~~>`, both `+` and `*` have higher precedence, and thus apply first.
Typically, figuring out the most convenient precedences for a group of operators requires some experimentation and a large collection of examples.

Following the new infix operator is a double arrow `=>`, which specifies the named function to be used for the infix operator.
Lean's standard library uses this feature to define `+` and `*` as infix operators that point at `HAdd.hAdd` and `HMul.hMul`, respectively, allowing type classes to be used to overload the infix operators.
Here, however, `andThen` is just an ordinary function.

Having defined an infix operator for `andThen`, `firstThird` can be rewritten in a way that brings the "pipeline" feeling of `none`-checks front and center:
```lean
{{#example_decl Examples/Monads.lean firstThirdInfix}}
```
This style is much more concise when writing larger functions:
```lean
{{#example_decl Examples/Monads.lean firstThirdFifthSeventInfix}}
```

## Propagating Error Messages

Pure functional languages such as Lean have no built-in exception mechanism for error handling, because throwing or catching an exception is outside of the step-by-step evaluation model for expressions.
However, functional programs certainly need to handle errors.
In the case of `firstThirdFifthSeventh`, it is likely relevant for a user to know just how long the list was and where the lookup failed.

This is typically accomplished by defining a datatype that can be either an error or a result, and translating functions with exceptions into functions that return this datatype:
```lean
{{#example_decl Examples/Monads.lean Except}}
```
The type variable `ε` stands for the type of errors that can be produced by the function.
Callers are expected to handle both errors and successes, which makes the type variable `ε` play a role that is a bit like that of a list of checked exceptions in Java.

Similarly to `Option`, `Except` can be used to indicate a failure to find an entry in a list.
In this case, the error type is a `String`:
```lean
{{#example_decl Examples/Monads.lean getExcept}}
```
Looking up an in-bounds value yields an `Except.ok`:
```lean
{{#example_decl Examples/Monads.lean ediblePlants}}

{{#example_in Examples/Monads.lean success}}
```
```output info
{{#example_out Examples/Monads.lean success}}
```
Looking up an out-of-bounds value yields an `Except.error`:
```lean
{{#example_in Examples/Monads.lean failure}}
```
```output info
{{#example_out Examples/Monads.lean failure}}
```

A single list lookup can conveniently return a value or an error:
```lean
{{#example_decl Examples/Monads.lean firstExcept}}
```
However, performing two list lookups requires handling potential failures:
```lean
{{#example_decl Examples/Monads.lean firstThirdExcept}}
```
Adding another list lookup to the function requires still more error handling:
```lean
{{#example_decl Examples/Monads.lean firstThirdFifthExcept}}
```
And one more list lookup begins to become quite unmanageable:
```lean
{{#example_decl Examples/Monads.lean firstThirdFifthSeventhExcept}}
```

Once again, a common pattern can be factored out into a helper.
Each step through the function checks for an error, and only proceeds with the rest of the computation if the result was a success.
A new version of `andThen` can be defined for `Except`:
```lean
{{#example_decl Examples/Monads.lean andThenExcept}}
```
Just as with `Option`, this version of `andThen` allows a more concise definition of `firstThird`:
```lean
{{#example_decl Examples/Monads.lean firstThirdAndThenExcept}}
```

In both the `Option` and `Except` case, there are two repeating patterns: there is the checking of intermediate results at each step, which has been factored out into `andThen`, and there is the final successful result, which is `some` or `Except.ok`, respectively.
For the sake of convenience, success can be factored out into a helper called `ok`:
```lean
{{#example_decl Examples/Monads.lean okExcept}}
```
Similarly, failure can be factored out into a helper called `fail`:
```lean
{{#example_decl Examples/Monads.lean failExcept}}
```
Using `ok` and `fail` makes `get` a little more readable:
```lean
{{#example_decl Examples/Monads.lean getExceptEffects}}
```


After adding the infix declaration for `andThen`, `firstThird` can be just as concise as the version that returns an `Option`:
```lean
{{#example_decl Examples/Monads.lean andThenExceptInfix}}

{{#example_decl Examples/Monads.lean firstThirdInfixExcept}}
```
The technique scales similarly to larger functions:
```lean
{{#example_decl Examples/Monads.lean firstThirdFifthSeventInfixExcept}}
```

## Logging

A number is even if dividing it by 2 leaves no remainder:
```lean
{{#example_decl Examples/Monads.lean isEven}}
```
The function `sumAndFindEvens` computes the sum of a list while remembering the even numbers encountered along the way:
```lean
{{#example_decl Examples/Monads.lean sumAndFindEvensDirect}}
```
This function is a simplified example of a common pattern.
Many programs need to traverse a data structure once, while both computing a main result and accumulating some kind of tertiary extra result.
One example of this is logging: a program that is an `IO` action can always log to a file on disk, but because the disk is outside of the mathematical world of Lean functions, it becomes much more difficult to prove things about logs based on `IO`.
Another example is a function that computes the sum of all the nodes in a tree with an inorder traversal, while simultaneously recording each nodes visited:
```lean
{{#example_decl Examples/Monads.lean inorderSum}}
```

Both `sumAndFindEvens` and `inorderSum` have a common repetitive structure.
Each step of computation returns a pair that consists of a list of data that have been saved along with the primary result.
The lists are then appended, and the primary result is computed and paired with the appended lists.
The common structure becomes more apparent with a small rewrite of `sumAndFindEvens` that more cleanly separates the concerns of saving even numbers and computing the sum:
```lean
{{#example_decl Examples/Monads.lean sumAndFindEvensDirectish}}
```

For the sake of clarity, a pair that consists of an accumulated result together with a value can be given its own name:
```lean
{{#example_decl Examples/Monads.lean WithLog}}
```
Similarly, the process of saving a list of accumulated results while passing a value on to the next step of a computation can be factored out into a helper, once again named `andThen`:
```lean
{{#example_decl Examples/Monads.lean andThenWithLog}}
```
In the case of errors, `ok` represents an operation that always succeeds.
Here, however, it is an operation that simply returns a value without logging anything:
```lean
{{#example_decl Examples/Monads.lean okWithLog}}
```
Just as `Except` provides `fail` as a possibility, `WithLog` should allow items to be added to a log.
This has no interesting return value associated with it, so it returns `Unit`:
```lean
{{#example_decl Examples/Monads.lean save}}
```

`WithLog`, `andThen`, `ok`, and `save` can be used to separate the logging concern from the summing concern in both programs:
```lean
{{#example_decl Examples/Monads.lean sumAndFindEvensAndThen}}

{{#example_decl Examples/Monads.lean inorderSumAndThen}}
```
And, once again, the infix operator helps put focus on the correct steps:
```lean
{{#example_decl Examples/Monads.lean infixAndThenLog}}

{{#example_decl Examples/Monads.lean withInfixLogging}}
```

## Numbering Tree Nodes

An _inorder numbering_ of a tree associates each data point in the tree with the step it would be visited at in an inorder traversal of the tree.
For example, consider `aTree`:
```lean
{{#example_decl Examples/Monads.lean aTree}}
```
Its inorder numbering is:
```output info
{{#example_out Examples/Monads.lean numberATree}}
```

Trees are most naturally processed with recursive functions, but the usual pattern of recursion on trees makes it difficult to compute an inorder numbering.
This is because the highest number assigned anywhere in the left subtree is used to determine the numbering of a node's data value, and then again to determine the starting point for numbering the right subtree.
In an imperative language, this issue can be worked around by using a mutable variable that contains the next number to be assigned.
The following Python program computes an inorder numbering using a mutable variable:
```python
{{#include ../../examples/inorder_python/inordernumbering.py:code}}
```
The numbering of the Python equivalent of `aTree` is:
```python
{{#include ../../examples/inorder_python/inordernumbering.py:a_tree}}
```
and its numbering is:
```
>>> {{#command {inorder_python} {inorderpy} {python inordernumbering.py} {number(a_tree)}}}
{{#command_out {inorderpy} {python inordernumbering.py} {inorder_python/expected} }}
```


Even though Lean does not have mutable variables, a workaround exists.
From the point of view of the rest of the world, the mutable variable can be thought of as having two relevant aspects: its value when the function is called, and its value when the function returns.
In other words, a function that uses a mutable variable can be seen as a function that takes the mutable variable's starting value as an argument, returning a pair of the variable's final value and the function's result.
This final value can then be passed as an argument to the next step.

Just as the Python example uses an outer function that establishes a mutable variable and an inner helper function that changes the variable, a Lean version of the function uses an outer function that provides the variable's starting value and explicitly returns the function's result along with an inner helper function that threads the variable's value while computing the numbered tree:
```lean
{{#example_decl Examples/Monads.lean numberDirect}}
```
This code, like the `none`-propagating `Option` code, the `error`-propagating `Except` code, and the log-accumulating `WithLog` code, commingles two concerns: propagating the value of the counter, and actually traversing the tree to find the result.
Just as in those cases, an `andThen` helper can be defined to propagate state from one step of a computation to another.
The first step is to give a name to the pattern of taking an input state as an argument and returning an output state together with a value:
```lean
{{#example_decl Examples/Monads.lean State}}
```

In the case of `State`, `ok` is a function that returns the input state unchanged, along with the provided value:
```lean
{{#example_decl Examples/Monads.lean okState}}
```
When working with a mutable variable, there are two fundamental operations: reading the value and replacing it with a new one.
Reading the current value is accomplished with a function that places the input state unmodified into the output state, and also places it into the value field:
```lean
{{#example_decl Examples/Monads.lean get}}
```
Writing a new value consists of ignoring the input state, and placing the provided new value into the output state:
```lean
{{#example_decl Examples/Monads.lean set}}
```
Finally, two computations that use state can be sequenced by finding both the output state and return value of the first function, then passing them both into the next function:
```lean
{{#example_decl Examples/Monads.lean andThenState}}
```

Using `State` and its helpers, local mutable state can be simulated:
```lean
{{#example_decl Examples/Monads.lean numberMonadicish}}
```
Because `State` simulates only a single local variable, `get` and `set` don't need to refer to any particular variable name.

## Monads: A Functional Design Pattern

Each of these examples has consisted of:
 * A polymorphic type, such as `Option`, `Except ε`, `WithLog logged`, or `State σ`
 * An operator `andThen` that takes care of some repetitive aspect of sequencing programs that have this type
 * An operator `ok` that is (in some sense) the most boring way to use the type
 * A collection of other operations, such as `none`, `fail`, `save`, and `get`, that name ways of using the type

This style of API is called a _monad_.
While the idea of monads is derived from a branch of mathematics called category theory, no understanding of category theory is needed in order to use them for programming.
The key idea of monads is that each monad encodes a particular kind of side effect using the tools provided by the pure functional language Lean.
For example, `Option` represents programs that can fail by returning `none`, `Except` represents programs that can throw exceptions, `WithLog` represents programs that accumulate a log while running, and `State` represents programs with a single mutable variable.

