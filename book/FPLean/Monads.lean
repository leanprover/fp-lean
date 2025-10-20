import VersoManual
import FPLean.Examples

import FPLean.Monads.Class
import FPLean.Monads.Arithmetic
import FPLean.Monads.Do
import FPLean.Monads.IO
import FPLean.Monads.Conveniences
import FPLean.Monads.Summary


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads"

#doc (Manual) "Monads" =>
%%%
tag := "monads"
%%%

In C# and Kotlin, the {CSharp}`?.` operator is a way to look up a property or call a method on a potentially-null value.
If the receiver is {CSharp}`null`, the whole expression is null.
Otherwise, the underlying non-{CSharp}`null` value receives the call.
Uses of {CSharp}`?.` can be chained, in which case the first {Kotlin}`null` result terminates the chain of lookups.
Chaining null-checks like this is much more convenient than writing and maintaining deeply nested {kw}`if`s.

Similarly, exceptions are significantly more convenient than manually checking and propagating error codes.
At the same time, logging is easiest to accomplish by having a dedicated logging framework, rather than having each function return both its log results and its return value.
Chained null checks and exceptions typically require language designers to anticipate this use case, while logging frameworks typically make use of side effects to decouple code that logs from the accumulation of the logs.

# One API, Many Applications
%%%
tag := "monad-api-examples"
%%%

All these features and more can be implemented in library code as instances of a common API called {moduleName}`Monad`.
Lean provides dedicated syntax that makes this API convenient to use, but can also get in the way of understanding what is going on behind the scenes.
This chapter begins with the nitty-gritty presentation of manually nesting null checks, and builds from there to the convenient, general API.
Please suspend your disbelief in the meantime.

## Checking for {lit}`none`: Don't Repeat Yourself
%%%
tag := "example-option-monad"
%%%

:::paragraph
In Lean, pattern matching can be used to chain checks for null.
Getting the first entry from a list can just use the optional indexing notation:

```anchor first
def first (xs : List α) : Option α :=
  xs[0]?
```
:::

:::paragraph
The result must be an {anchorName first}`Option` because empty lists have no first entry.
Extracting the first and third entries requires a check that each is not {moduleName}`none`:

```anchor firstThird
def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)
```
Similarly, extracting the first, third, and fifth entries requires more checks that the values are not {moduleName}`none`:

```anchor firstThirdFifth
def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        some (first, third, fifth)
```
And adding the seventh entry to this sequence begins to become quite unmanageable:

```anchor firstThirdFifthSeventh
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        match xs[6]? with
        | none => none
        | some seventh =>
          some (first, third, fifth, seventh)
```
:::

:::paragraph
The fundamental problem with this code is that it addresses two concerns: extracting the numbers and checking that all of them are present.
The second concern is addressed by copying and pasting the code that handles the {moduleName}`none` case.
It is often good style to lift a repetitive segment into a helper function:

```anchor andThenOption
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x
```
This helper, which is used similarly to {CSharp}`?.` in C# and Kotlin, takes care of propagating {moduleName}`none` values.
It takes two arguments: an optional value and a function to apply when the value is not {moduleName}`none`.
If the first argument is {moduleName}`none`, then the helper returns {moduleName}`none`.
If the first argument is not {moduleName}`none`, then the function is applied to the contents of the {moduleName}`some` constructor.
:::

:::paragraph
Now, {anchorName firstThirdandThen}`firstThird` can be rewritten to use {anchorName firstThirdandThen}`andThen` instead of pattern matching:

```anchor firstThirdandThen
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)
```
In Lean, functions don't need to be enclosed in parentheses when passed as arguments.
The following equivalent definition uses more parentheses and indents the bodies of functions:

```anchor firstThirdandThenExpl
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))
```
The {anchorName firstThirdandThenExpl}`andThen` helper provides a sort of “pipeline” through which values flow, and the version with the somewhat unusual indentation is more suggestive of this fact.
Improving the syntax used to write {anchorName firstThirdandThenExpl}`andThen` can make these computations even easier to understand.
:::

### Infix Operators
%%%
tag := "defining-infix-operators"
%%%


In Lean, infix operators can be declared using the {kw}`infix`, {kw}`infixl`, and {kw}`infixr` commands, which create (respectively) non-associative, left-associative, and right-associative operators.
When used multiple times in a row, a {deftech}_left associative_ operator stacks up the opening parentheses on the left side of the expression.
The addition operator {lit}`+` is left associative, so {anchorTerm plusFixity}`w + x + y + z` is equivalent to {anchorTerm plusFixity}`(((w + x) + y) + z)`.
The exponentiation operator {lit}`^` is right associative, so {anchorTerm powFixity}`w ^ x ^ y ^ z` is equivalent to {anchorTerm powFixity}`w ^ (x ^ (y ^ z))`.
Comparison operators such as {lit}`<` are non-associative, so {lit}`x < y < z` is a syntax error and requires manual parentheses.

:::paragraph
The following declaration makes {anchorName andThenOptArr}`andThen` into an infix operator:

```anchor andThenOptArr
infixl:55 " ~~> " => andThen
```
The number following the colon declares the {deftech}_precedence_ of the new infix operator.
In ordinary mathematical notation, {anchorTerm plusTimesPrec}`x + y * z` is equivalent to {anchorTerm plusTimesPrec}`x + (y * z)` even though both {lit}`+` and {lit}`*` are left associative.
In Lean, {lit}`+` has precedence 65 and {lit}`*` has precedence 70.
Higher-precedence operators are applied before lower-precedence operators.
According to the declaration of {lit}`~~>`, both {lit}`+` and {lit}`*` have higher precedence, and thus apply first.
Typically, figuring out the most convenient precedences for a group of operators requires some experimentation and a large collection of examples.
:::

Following the new infix operator is a double arrow {lit}`=>`, which specifies the named function to be used for the infix operator.
Lean's standard library uses this feature to define {lit}`+` and {lit}`*` as infix operators that point at {moduleName}`HAdd.hAdd` and {moduleName}`HMul.hMul`, respectively, allowing type classes to be used to overload the infix operators.
Here, however, {anchorName firstThirdandThen}`andThen` is just an ordinary function.

:::paragraph
Having defined an infix operator for {anchorName andThenOptArr}`andThen`, {anchorName firstThirdInfix (show := firstThird)}`firstThirdInfix` can be rewritten in a way that brings the “pipeline” feeling of {moduleName}`none`-checks front and center:

```anchor firstThirdInfix
def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)
```
This style is much more concise when writing larger functions:
```anchor firstThirdFifthSeventInfix
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)
```
:::

## Propagating Error Messages
%%%
tag := "example-except-monad"
%%%

Pure functional languages such as Lean have no built-in exception mechanism for error handling, because throwing or catching an exception is outside of the step-by-step evaluation model for expressions.
However, functional programs certainly need to handle errors.
In the case of {anchorName firstThirdFifthSeventInfix}`firstThirdFifthSeventh`, it is likely relevant for a user to know just how long the list was and where the lookup failed.

:::paragraph
This is typically accomplished by defining a datatype that can be either an error or a result, and translating functions with exceptions into functions that return this datatype:

```anchor Except
inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α
deriving BEq, Hashable, Repr
```
The type variable {anchorName Except}`ε` stands for the type of errors that can be produced by the function.
Callers are expected to handle both errors and successes, which makes the type variable {anchorName Except}`ε` play a role that is a bit like that of a list of checked exceptions in Java.
:::

:::paragraph
Similarly to {anchorName first}`Option`, {anchorName Except}`Except` can be used to indicate a failure to find an entry in a list.
In this case, the error type is a {moduleName}`String`:

```anchor getExcept
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x
```
Looking up an in-bounds value yields an {anchorName ExceptExtra}`Except.ok`:
```anchor ediblePlants
def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]
```
```anchor success
#eval get ediblePlants 2
```
```anchorInfo success
Except.ok "sea buckthorn"
```
Looking up an out-of-bounds value yields an {anchorName ExceptExtra}`Except.error`:
```anchor failure
#eval get ediblePlants 4
```
```anchorInfo failure
Except.error "Index 4 not found (maximum is 3)"
```
:::

:::paragraph
A single list lookup can conveniently return a value or an error:
```anchor firstExcept
def first (xs : List α) : Except String α :=
  get xs 0
```
However, performing two list lookups requires handling potential failures:
```anchor firstThirdExcept
def firstThird (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      Except.ok (first, third)
```
Adding another list lookup to the function requires still more error handling:
```anchor firstThirdFifthExcept
def firstThirdFifth (xs : List α) : Except String (α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        Except.ok (first, third, fifth)
```
And one more list lookup begins to become quite unmanageable:
```anchor firstThirdFifthSeventhExcept
def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        match get xs 6 with
        | Except.error msg => Except.error msg
        | Except.ok seventh =>
          Except.ok (first, third, fifth, seventh)
```
:::

:::paragraph
Once again, a common pattern can be factored out into a helper.
Each step through the function checks for an error, and only proceeds with the rest of the computation if the result was a success.
A new version of {anchorName andThenExcept}`andThen` can be defined for {anchorName andThenExcept}`Except`:

```anchor andThenExcept
def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x
```
Just as with {anchorName first}`Option`, this version of {anchorName andThenExcept}`andThen` allows a more concise definition of {anchorName firstThirdAndThenExcept}`firstThird'`:

```anchor firstThirdAndThenExcept
def firstThird' (xs : List α) : Except String (α × α) :=
  andThen (get xs 0) fun first  =>
  andThen (get xs 2) fun third =>
  Except.ok (first, third)
```
:::

:::paragraph
In both the {anchorName first}`Option` and {anchorName andThenExcept}`Except` case, there are two repeating patterns: there is the checking of intermediate results at each step, which has been factored out into {anchorName andThenExcept}`andThen`, and there is the final successful result, which is {moduleName}`some` or {anchorName andThenExcept}`Except.ok`, respectively.
For the sake of convenience, success can be factored out into a helper called {anchorName okExcept}`ok`:

```anchor okExcept
def ok (x : α) : Except ε α := Except.ok x
```
Similarly, failure can be factored out into a helper called {anchorName failExcept}`fail`:

```anchor failExcept
def fail (err : ε) : Except ε α := Except.error err
```
Using {anchorName okExcept}`ok` and {anchorName failExcept}`fail` makes {anchorName getExceptEffects}`get` a little more readable:

```anchor getExceptEffects
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x
```
:::

:::paragraph
After adding the infix declaration for {anchorName andThenExceptInfix}`andThen`, {anchorName firstThirdInfixExcept}`firstThird` can be just as concise as the version that returns an {anchorName first}`Option`:

```anchor andThenExceptInfix
infixl:55 " ~~> " => andThen
```

```anchor firstThirdInfixExcept
def firstThird (xs : List α) : Except String (α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  ok (first, third)
```
The technique scales similarly to larger functions:

```anchor firstThirdFifthSeventInfixExcept
def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)
```

:::

## Logging
%%%
tag := "logging"
%%%

:::paragraph
A number is even if dividing it by 2 leaves no remainder:
```anchor isEven
def isEven (i : Int) : Bool :=
  i % 2 == 0
```
The function {anchorName sumAndFindEvensDirect}`sumAndFindEvens` computes the sum of a list while remembering the even numbers encountered along the way:
```anchor sumAndFindEvensDirect
def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    (if isEven i then i :: moreEven else moreEven, sum + i)
```
:::

:::paragraph
This function is a simplified example of a common pattern.
Many programs need to traverse a data structure once, while both computing a main result and accumulating some kind of tertiary extra result.
One example of this is logging: a program that is an {moduleName}`IO` action can always log to a file on disk, but because the disk is outside of the mathematical world of Lean functions, it becomes much more difficult to prove things about logs based on {moduleName}`IO`.
Another example is a function that computes the sum of all the nodes in a tree with an inorder traversal, while simultaneously recording each nodes visited:

```anchor inorderSum
def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum) := inorderSum l
    let (hereVisited, hereSum) := ([x], x)
    let (rightVisited, rightSum) := inorderSum r
    (leftVisited ++ hereVisited ++ rightVisited,
     leftSum + hereSum + rightSum)
```
:::

Both {anchorName sumAndFindEvensDirect}`sumAndFindEvens` and {anchorName inorderSum}`inorderSum` have a common repetitive structure.
Each step of computation returns a pair that consists of a list of data that have been saved along with the primary result.
The lists are then appended, and the primary result is computed and paired with the appended lists.
The common structure becomes more apparent with a small rewrite of {anchorName sumAndFindEvensDirectish}`sumAndFindEvens` that more cleanly separates the concerns of saving even numbers and computing the sum:

```anchor sumAndFindEvensDirectish
def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    let (evenHere, ()) := (if isEven i then [i] else [], ())
    (evenHere ++ moreEven, sum + i)
```

For the sake of clarity, a pair that consists of an accumulated result together with a value can be given its own name:

```anchor WithLog
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
```
Similarly, the process of saving a list of accumulated results while passing a value on to the next step of a computation can be factored out into a helper, once again named {anchorName andThenWithLog}`andThen`:

```anchor andThenWithLog
def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}
```
In the case of errors, {anchorName okWithLog}`ok` represents an operation that always succeeds.
Here, however, it is an operation that simply returns a value without logging anything:

```anchor okWithLog
def ok (x : β) : WithLog α β := {log := [], val := x}
```
Just as {anchorName Except}`Except` provides {anchorName failExcept}`fail` as a possibility, {anchorName WithLog}`WithLog` should allow items to be added to a log.
This has no interesting return value associated with it, so it returns {anchorName save}`Unit`:

```anchor save
def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}
```

{anchorName WithLog}`WithLog`, {anchorName andThenWithLog}`andThen`, {anchorName okWithLog}`ok`, and {anchorName save}`save` can be used to separate the logging concern from the summing concern in both programs:

```anchor sumAndFindEvensAndThen
def sumAndFindEvens : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    andThen (if isEven i then save i else ok ()) fun () =>
    andThen (sumAndFindEvens is) fun sum =>
    ok (i + sum)
```

```anchor inorderSumAndThen
def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    andThen (inorderSum l) fun leftSum =>
    andThen (save x) fun () =>
    andThen (inorderSum r) fun rightSum =>
    ok (leftSum + x + rightSum)
```
And, once again, the infix operator helps put focus on the correct steps:

```anchor infixAndThenLog
infixl:55 " ~~> " => andThen
```

```anchor withInfixLogging
def sumAndFindEvens : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    (if isEven i then save i else ok ()) ~~> fun () =>
    sumAndFindEvens is ~~> fun sum =>
    ok (i + sum)

def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    inorderSum l ~~> fun leftSum =>
    save x ~~> fun () =>
    inorderSum r ~~> fun rightSum =>
    ok (leftSum + x + rightSum)
```

## Numbering Tree Nodes
%%%
tag := "numbering-tree-nodes"
%%%

An {deftech}_inorder numbering_ of a tree associates each data point in the tree with the step it would be visited at in an inorder traversal of the tree.
For example, consider {anchorName aTree}`aTree`:

```anchor aTree
open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)
```
Its inorder numbering is:
```anchorInfo numberATree
BinTree.branch
  (BinTree.branch
    (BinTree.branch (BinTree.leaf) (0, "a") (BinTree.branch (BinTree.leaf) (1, "b") (BinTree.leaf)))
    (2, "c")
    (BinTree.leaf))
  (3, "d")
  (BinTree.branch (BinTree.leaf) (4, "e") (BinTree.leaf))
```

:::paragraph
Trees are most naturally processed with recursive functions, but the usual pattern of recursion on trees makes it difficult to compute an inorder numbering.
This is because the highest number assigned anywhere in the left subtree is used to determine the numbering of a node's data value, and then again to determine the starting point for numbering the right subtree.
In an imperative language, this issue can be worked around by using a mutable variable that contains the next number to be assigned.
The following Python program computes an inorder numbering using a mutable variable:
```includePython "../examples/inorder_python/inordernumbering.py" (anchor := code)
class Branch:
    def __init__(self, value, left=None, right=None):
        self.left = left
        self.value = value
        self.right = right
    def __repr__(self):
        return f'Branch({self.value!r}, left={self.left!r}, right={self.right!r})'

def number(tree):
    num = 0
    def helper(t):
        nonlocal num
        if t is None:
            return None
        else:
            new_left = helper(t.left)
            new_value = (num, t.value)
            num += 1
            new_right = helper(t.right)
            return Branch(left=new_left, value=new_value, right=new_right)

    return helper(tree)
```
The numbering of the Python equivalent of {anchorName aTree}`aTree` is:
```includePython "../examples/inorder_python/inordernumbering.py" (anchor := a_tree)
a_tree = Branch("d",
                left=Branch("c",
                            left=Branch("a", left=None, right=Branch("b")),
                            right=None),
                right=Branch("e"))
```
and its numbering is:
```command inorderpy "inorder_python" (prompt := ">>> ") (show := "number(a_tree)")
python3 inordernumbering.py
```
```commandOut inorderpy "python3 inordernumbering.py"
Branch((3, 'd'), left=Branch((2, 'c'), left=Branch((0, 'a'), left=None, right=Branch((1, 'b'), left=None, right=None)), right=None), right=Branch((4, 'e'), left=None, right=None))
```
:::


Even though Lean does not have mutable variables, a workaround exists.
From the point of view of the rest of the world, the mutable variable can be thought of as having two relevant aspects: its value when the function is called, and its value when the function returns.
In other words, a function that uses a mutable variable can be seen as a function that takes the mutable variable's starting value as an argument, returning a pair of the variable's final value and the function's result.
This final value can then be passed as an argument to the next step.

:::paragraph
Just as the Python example uses an outer function that establishes a mutable variable and an inner helper function that changes the variable, a Lean version of the function uses an outer function that provides the variable's starting value and explicitly returns the function's result along with an inner helper function that threads the variable's value while computing the numbered tree:

```anchor numberDirect
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf => (n, BinTree.leaf)
    | BinTree.branch left x right =>
      let (k, numberedLeft) := helper n left
      let (i, numberedRight) := helper (k + 1) right
      (i, BinTree.branch numberedLeft (k, x) numberedRight)
  (helper 0 t).snd
```
This code, like the {moduleName}`none`-propagating {anchorName first}`Option` code, the {anchorName exceptNames (show := error)}`Except.error`-propagating {anchorName exceptNames}`Except` code, and the log-accumulating {moduleName}`WithLog` code, commingles two concerns: propagating the value of the counter, and actually traversing the tree to find the result.
Just as in those cases, an {anchorName andThenState}`andThen` helper can be defined to propagate state from one step of a computation to another.
The first step is to give a name to the pattern of taking an input state as an argument and returning an output state together with a value:

```anchor State
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)
```
:::

:::paragraph
In the case of {anchorName State}`State`, {anchorName okState}`ok` is a function that returns the input state unchanged, along with the provided value:
```anchor okState
def ok (x : α) : State σ α :=
  fun s => (s, x)
```
:::

:::paragraph
When working with a mutable variable, there are two fundamental operations: reading the value and replacing it with a new one.
Reading the current value is accomplished with a function that places the input state unmodified into the output state, and also places it into the value field:
```anchor get
def get : State σ σ :=
  fun s => (s, s)
```
Writing a new value consists of ignoring the input state, and placing the provided new value into the output state:
```anchor set
def set (s : σ) : State σ Unit :=
  fun _ => (s, ())
```
:::

:::paragraph
Finally, two computations that use state can be sequenced by finding both the output state and return value of the first function, then passing them both into the next function:

```anchor andThenState
def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => andThen
```
:::

:::paragraph
Using {anchorName State}`State` and its helpers, local mutable state can be simulated:

```anchor numberMonadicish
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => ok BinTree.leaf
    | BinTree.branch left x right =>
      helper left ~~> fun numberedLeft =>
      get ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper right ~~> fun numberedRight =>
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd
```
Because {anchorName State}`State` simulates only a single local variable, {anchorName get}`get` and {anchorName set}`set` don't need to refer to any particular variable name.
:::

## Monads: A Functional Design Pattern
%%%
tag := "monad-as-design-pattern"
%%%

Each of these examples has consisted of:
 * A polymorphic type, such as {anchorName first}`Option`, {anchorTerm okExcept}`Except ε`, {anchorTerm save}`WithLog α`, or {anchorTerm andThenState}`State σ`
 * An operator {lit}`andThen` that takes care of some repetitive aspect of sequencing programs that have this type
 * An operator {lit}`ok` that is (in some sense) the most boring way to use the type
 * A collection of other operations, such as {moduleName}`none`, {anchorName failExcept}`fail`, {anchorName save}`save`, and {anchorName get}`get`, that name ways of using the type

This style of API is called a {deftech}_monad_.
While the idea of monads is derived from a branch of mathematics called category theory, no understanding of category theory is needed in order to use them for programming.
The key idea of monads is that each monad encodes a particular kind of side effect using the tools provided by the pure functional language Lean.
For example, {anchorName first}`Option` represents programs that can fail by returning {moduleName}`none`, {moduleName}`Except` represents programs that can throw exceptions, {moduleName}`WithLog` represents programs that accumulate a log while running, and {anchorName State}`State` represents programs with a single mutable variable.

{include 1 FPLean.Monads.Class}

{include 1 FPLean.Monads.Arithmetic}

{include 1 FPLean.Monads.Do}

{include 1 FPLean.Monads.IO}

{include 1 FPLean.Monads.Conveniences}

{include 1 FPLean.Monads.Summary}
