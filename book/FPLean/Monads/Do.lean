import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Do"

#doc (Manual) "{kw}`do`-Notation for Monads" =>

While APIs based on monads are very powerful, the explicit use of `>>=` with anonymous functions is still somewhat noisy.
Just as infix operators are used instead of explicit calls to `HAdd.hAdd`, Lean provides a syntax for monads called _{kw}`do`-notation_ that can make programs that use monads easier to read and write.
This is the very same {kw}`do`-notation that is used to write programs in `IO`, and `IO` is also a monad.

In {ref "hello-world"}[Hello, World!], the {kw}`do` syntax is used to combine `IO` actions, but the meaning of these programs is explained directly.
Understanding how to program with monads means that {kw}`do` can now be explained in terms of how it translates into uses of the underlying monad operators.

The first translation of {kw}`do` is used when the only statement in the {kw}`do` is a single expression `E`.
In this case, the {kw}`do` is removed, so
```anchor doSugar1a
do E
```
translates to
```anchor doSugar1b
E
```

The second translation is used when the first statement of the {kw}`do` is a {kw}`let` with an arrow, binding a local variable.
This translates to a use of `>>=` together with a function that binds that very same variable, so
```anchor doSugar2a
 do let x ← E₁
    Stmt
    ...
    Eₙ
```
translates to
```anchor doSugar2b
E₁ >>= fun x =>
  do Stmt
     ...
     Eₙ
```

When the first statement of the {kw}`do` block is an expression, then it is considered to be a monadic action that returns `Unit`, so the function matches the `Unit` constructor and
```anchor doSugar3a
  do E₁
     Stmt
     ...
     Eₙ
```
translates to
```anchor doSugar3b
E₁ >>= fun () =>
  do Stmt
     ...
     Eₙ
```

Finally, when the first statement of the {kw}`do` block is a {kw}`let` that uses `:=`, the translated form is an ordinary let expression, so
```anchor doSugar4a
do let x := E₁
   Stmt
   ...
   Eₙ
```
translates to
```anchor doSugar4b
let x := E₁
do Stmt
   ...
   Eₙ
```

The definition of `firstThirdFifthSeventh` that uses the `Monad` class looks like this:

```anchor firstThirdFifthSeventhMonad (module := Examples.Monads.Class)
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)
```
Using {kw}`do`-notation, it becomes significantly more readable:

```anchor firstThirdFifthSeventhDo
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)
```

Without the `Monad` type class, the function `number` that numbers the nodes of a tree was written:

```anchor numberMonadicish (module := Examples.Monads)
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
With `Monad` and {kw}`do`, its definition is much less noisy:

```anchor numberDo
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      let numberedLeft ← helper left
      let n ← get
      set (n + 1)
      let numberedRight ← helper right
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd
```


All of the conveniences from {kw}`do` with `IO` are also available when using it with other monads.
For example, nested actions also work in any monad.
The original definition of `mapM` was:

```anchor mapM (module := Examples.Monads.Class)
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
```
With {kw}`do`-notation, it can be written:

```anchor mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM f xs
    pure (hd :: tl)
```
Using nested actions makes it almost as short as the original non-monadic `map`:

```anchor mapMNested
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    pure ((← f x) :: (← mapM f xs))
```
Using nested actions, `number` can be made much more concise:

```anchor numberDoShort
def increment : State Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      pure (BinTree.branch (← helper left) ((← increment), x) (← helper right))
  (helper t 0).snd
```



# Exercises

 * Rewrite `evaluateM`, its helpers, and the different specific use cases using {kw}`do`-notation instead of explicit calls to `>>=`.
 * Rewrite `firstThirdFifthSeventh` using nested actions.
