import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "The Applicative Contract" =>
%%%
tag := "applicative-laws"
%%%

Just like {anchorName ApplicativeLaws}`Functor`, {anchorName ApplicativeLaws}`Monad`, and types that implement {anchorName SizedCreature}`BEq` and {anchorName MonstrousAssistantMore}`Hashable`, {anchorName ApplicativeLaws}`Applicative` has a set of rules that all instances should adhere to.

There are four rules that an applicative functor should follow:
1. It should respect identity, so {anchorTerm ApplicativeLaws}`pure id <*> v = v`
2. It should respect function composition, so {anchorTerm ApplicativeLaws}`pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`
3. Sequencing pure operations should be a no-op, so {anchorTerm ApplicativeLaws}`pure f <*> pure x`{lit}` = `{anchorTerm ApplicativeLaws}`pure (f x)`
4. The ordering of pure operations doesn't matter, so {anchorTerm ApplicativeLaws}`u <*> pure x = pure (fun f => f x) <*> u`

To check these for the {anchorTerm ApplicativeOption}`Applicative Option` instance, start by expanding {anchorName ApplicativeLaws}`pure` into {anchorName ApplicativeOption}`some`.

The first rule states that {anchorTerm ApplicativeOptionLaws1}`some id <*> v = v`.
The definition of {anchorName fakeSeq}`seq` for {anchorName ApplicativeOption}`Option` states that this is the same as {anchorTerm ApplicativeOptionLaws1}`id <$> v = v`, which is one of the {anchorName ApplicativeLaws}`Functor` rules that have already been checked.

The second rule states that {anchorTerm ApplicativeOptionLaws2}`some (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`.
If any of {anchorName ApplicativeOptionLaws2}`u`, {anchorName ApplicativeOptionLaws2}`v`, or {anchorName ApplicativeOptionLaws2}`w` is {anchorName ApplicativeOption}`none`, then both sides are {anchorName ApplicativeOption}`none`, so the property holds.
Assuming that {anchorName ApplicativeOptionLaws2}`u` is {anchorTerm OptionHomomorphism1}`some f`, that {anchorName ApplicativeOptionLaws2}`v` is {anchorTerm OptionHomomorphism1}`some g`, and that {anchorName ApplicativeOptionLaws2}`w` is {anchorTerm OptionHomomorphism1}`some x`, then this is equivalent to saying that {anchorTerm OptionHomomorphism}`some (· ∘ ·) <*> some f <*> some g <*> some x = some f <*> (some g <*> some x)`.
Evaluating the two sides yields the same result:
```anchorEvalSteps OptionHomomorphism1
some (· ∘ ·) <*> some f <*> some g <*> some x
===>
some (f ∘ ·) <*> some g <*> some x
===>
some (f ∘ g) <*> some x
===>
some ((f ∘ g) x)
===>
some (f (g x))
```
```anchorEvalSteps OptionHomomorphism2
some f <*> (some g <*> some x)
===>
some f <*> (some (g x))
===>
some (f (g x))
```

The third rule follows directly from the definition of {anchorName fakeSeq}`seq`:
```anchorEvalSteps OptionPureSeq
some f <*> some x
===>
f <$> some x
===>
some (f x)
```

In the fourth case, assume that {anchorName ApplicativeLaws}`u` is {anchorTerm OptionPureSeq}`some f`, because if it's {anchorName AlternativeOption}`none`, both sides of the equation are {anchorName AlternativeOption}`none`.
{anchorTerm OptionPureSeq}`some f <*> some x` evaluates directly to {anchorTerm OptionPureSeq}`some (f x)`, as does {anchorTerm OptionPureSeq2}`some (fun g => g x) <*> some f`.


# All Applicatives are Functors
%%%
tag := "applicatives-are-functors"
%%%

The two operators for {anchorName ApplicativeMap}`Applicative` are enough to define {anchorName ApplicativeMap}`map`:

```anchor ApplicativeMap
def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x
```

This can only be used to implement {anchorName ApplicativeLaws}`Functor` if the contract for {anchorName ApplicativeLaws}`Applicative` guarantees the contract for {anchorName ApplicativeLaws}`Functor`, however.
The first rule of {anchorName ApplicativeLaws}`Functor` is that {anchorTerm AppToFunTerms}`id <$> x = x`, which follows directly from the first rule for {anchorName ApplicativeLaws}`Applicative`.
The second rule of {anchorName ApplicativeLaws}`Functor` is that {anchorTerm AppToFunTerms}`map (f ∘ g) x = map f (map g x)`.
Unfolding the definition of {anchorName AppToFunTerms}`map` here results in {anchorTerm AppToFunTerms}`pure (f ∘ g) <*> x = pure f <*> (pure g <*> x)`.
Using the rule that sequencing pure operations is a no-op, the left side can be rewritten to {anchorTerm AppToFunTerms}`pure (· ∘ ·) <*> pure f <*> pure g <*> x`.
This is an instance of the rule that states that applicative functors respect function composition.

This justifies a definition of {anchorName ApplicativeMap}`Applicative` that extends {anchorName ApplicativeLaws}`Functor`, with a default definition of {anchorTerm ApplicativeExtendsFunctorOne}`map` given in terms of {anchorName ApplicativeExtendsFunctorOne}`pure` and {anchorName ApplicativeExtendsFunctorOne}`seq`:

```anchor ApplicativeExtendsFunctorOne
class Applicative (f : Type → Type) extends Functor f where
  pure : α → f α
  seq : f (α → β) → (Unit → f α) → f β
  map g x := seq (pure g) (fun () => x)
```

# All Monads are Applicative Functors
%%%
tag :="monads-are-applicative"
%%%

An instance of {anchorName MonadExtends}`Monad` already requires an implementation of {anchorName MonadSeq}`pure`.
Together with {anchorName MonadExtends}`bind`, this is enough to define {anchorName MonadSeq}`seq`:

```anchor MonadSeq
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)
```
Once again, checking that the {anchorName MonadSeq}`Monad` contract implies the {anchorName MonadExtends}`Applicative` contract will allow this to be used as a default definition for {anchorTerm MonadExtends}`seq` if {anchorName MonadSeq}`Monad` extends {anchorName MonadExtends}`Applicative`.

The rest of this section consists of an argument that this implementation of {anchorTerm MonadExtends}`seq` based on {anchorName MonadExtends}`bind` in fact satisfies the {anchorName MonadExtends}`Applicative` contract.
One of the beautiful things about functional programming is that this kind of argument can be worked out on a piece of paper with a pencil, using the kinds of evaluation rules from {ref "evaluating"}[the initial section on evaluating expressions].
Thinking about the meanings of the operations while reading these arguments can sometimes help with understanding.

Replacing {kw}`do`-notation with explicit uses of {lit}`>>=` makes it easier to apply the {anchorName MonadSeqDesugar}`Monad` rules:

```anchor MonadSeqDesugar
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  f >>= fun g =>
  x () >>= fun y =>
  pure (g y)
```


To check that this definition respects identity, check that {anchorTerm mSeqRespIdInit}`seq (pure id) (fun () => v) = v`.
The left hand side is equivalent to {anchorTerm mSeqRespIdInit}`pure id >>= fun g => (fun () => v) () >>= fun y => pure (g y)`.
The unit function in the middle can be eliminated immediately, yielding {anchorTerm mSeqRespIdInit}`pure id >>= fun g => v >>= fun y => pure (g y)`.
Using the fact that {anchorName mSeqRespIdInit}`pure` is a left identity of {anchorTerm mSeqRespIdInit}`>>=`, this is the same as {anchorTerm mSeqRespIdInit}`v >>= fun y => pure (id y)`, which is {anchorTerm mSeqRespIdInit}`v >>= fun y => pure y`.
Because {anchorTerm mSeqRespIdInit}`fun x => f x` is the same as {anchorName mSeqRespIdInit}`f`, this is the same as {anchorTerm mSeqRespIdInit}`v >>= pure`, and the fact that {anchorName mSeqRespIdInit}`pure` is a right identity of {anchorTerm mSeqRespIdInit}`>>=` can be used to get {anchorName mSeqRespIdInit}`v`.

This kind of informal reasoning can be made easier to read with a bit of reformatting.
In the following chart, read “{lit}`EXPR1 ={ REASON }= EXPR2`” as “{lit}`EXPR1` is the same as {lit}`EXPR2` because {lit}`REASON`”:

```anchorEqSteps mSeqRespId
pure id >>= fun g => v >>= fun y => pure (g y)
={
/-- `pure` is a left identity of `>>=` -/
by simp [LawfulMonad.pure_bind]
}=
v >>= fun y => pure (id y)
={
/-- Reduce the call to `id` -/
}=
v >>= fun y => pure y
={
/-- `fun x => f x` is the same as `f` -/
by
  have {α β } {f : α → β} : (fun x => f x) = (f) := rfl
  rfl
}=
v >>= pure
={
/-- `pure` is a right identity of `>>=` -/
by simp
}=
v
```



To check that it respects function composition, check that {anchorTerm ApplicativeLaws}`pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`.
The first step is to replace {lit}`<*>` with this definition of {anchorName MonadSeqDesugar}`seq`.
After that, a (somewhat long) series of steps that use the identity and associativity rules from the {anchorName ApplicativeLaws}`Monad` contract is enough to get from one to the other:
```anchorEqSteps mSeqRespComp
seq (seq (seq (pure (· ∘ ·)) (fun _ => u))
      (fun _ => v))
  (fun _ => w)
={
/-- Definition of `seq` -/
}=
((pure (· ∘ ·) >>= fun f =>
   u >>= fun x =>
   pure (f x)) >>= fun g =>
  v >>= fun y =>
  pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- `pure` is a left identity of `>>=` -/
by simp only [LawfulMonad.pure_bind]
}=
((u >>= fun x =>
   pure (x ∘ ·)) >>= fun g =>
   v >>= fun y =>
  pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- Insertion of parentheses for clarity -/
}=
((u >>= fun x =>
   pure (x ∘ ·)) >>= (fun g =>
   v >>= fun y =>
  pure (g y))) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- Associativity of `>>=` -/
by simp only [LawfulMonad.bind_assoc]
}=
(u >>= fun x =>
  pure (x ∘ ·) >>= fun g =>
 v  >>= fun y => pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- `pure` is a left identity of `>>=` -/
by simp only [LawfulMonad.pure_bind]
}=
(u >>= fun x =>
  v >>= fun y =>
  pure (x ∘ y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- Associativity of `>>=` -/
by simp only [LawfulMonad.bind_assoc]
}=
u >>= fun x =>
v >>= fun y =>
pure (x ∘ y) >>= fun h =>
w >>= fun z =>
pure (h z)
={
/-- `pure` is a left identity of `>>=` -/
by simp [bind_pure_comp]; rfl
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure ((x ∘ y) z)
={
/-- Definition of function composition -/
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure (x (y z))
={
/--
Time to start moving backwards!
`pure` is a left identity of `>>=`
-/
by simp
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure (y z) >>= fun q =>
pure (x q)
={
/-- Associativity of `>>=` -/
by simp
}=
u >>= fun x =>
v >>= fun y =>
 (w >>= fun p =>
  pure (y p)) >>= fun q =>
 pure (x q)
={
/-- Associativity of `>>=` -/
by simp
}=
u >>= fun x =>
 (v >>= fun y =>
  w >>= fun q =>
  pure (y q)) >>= fun z =>
 pure (x z)
={
/-- This includes the definition of `seq` -/
}=
u >>= fun x =>
seq v (fun () => w) >>= fun q =>
pure (x q)
={
/-- This also includes the definition of `seq` -/
}=
seq u (fun () => seq v (fun () => w))
```


To check that sequencing pure operations is a no-op:
```anchorEqSteps mSeqPureNoOp
seq (pure f) (fun () => pure x)
={
/-- Replacing `seq` with its definition -/
}=
pure f >>= fun g =>
pure x >>= fun y =>
pure (g y)
={
/-- `pure` is a left identity of `>>=` -/
by simp
}=
pure f >>= fun g =>
pure (g x)
={
/-- `pure` is a left identity of `>>=` -/
by simp
}=
pure (f x)
```


And finally, to check that the ordering of pure operations doesn't matter:
```anchorEqSteps mSeqPureNoOrder
seq u (fun () => pure x)
={
/-- Definition of `seq` -/
}=
u >>= fun f =>
pure x >>= fun y =>
pure (f y)
={
/-- `pure` is a left identity of `>>=` -/
by simp
}=
u >>= fun f =>
pure (f x)
={
/-- Clever replacement of one expression by an equivalent one that makes the rule match -/
}=
u >>= fun f =>
pure ((fun g => g x) f)
={
/-- `pure` is a left identity of `>>=` -/
by simp [LawfulMonad.pure_bind]
}=
pure (fun g => g x) >>= fun h =>
u >>= fun f =>
pure (h f)
={
/-- Definition of `seq` -/
}=
seq (pure (fun f => f x)) (fun () => u)
```


This justifies a definition of {anchorName ApplicativeLaws}`Monad` that extends {anchorName ApplicativeLaws}`Applicative`, with a default definition of {anchorTerm MonadExtends}`seq`:

```anchor MonadExtends
class Monad (m : Type → Type) extends Applicative m where
  bind : m α → (α → m β) → m β
  seq f x :=
    bind f fun g =>
    bind (x ()) fun y =>
    pure (g y)
```
{anchorName MonadExtends}`Applicative`'s own default definition of {anchorTerm ApplicativeExtendsFunctorOne}`map` means that every {anchorName MonadExtends}`Monad` instance automatically generates {anchorName MonadExtends}`Applicative` and {anchorName ApplicativeExtendsFunctorOne}`Functor` instances as well.

# Additional Stipulations
%%%
tag := "additional-stipulations"
%%%

In addition to adhering to the individual contracts associated with each type class, combined implementations {anchorName ApplicativeLaws}`Functor`, {anchorName ApplicativeLaws}`Applicative` and {anchorName ApplicativeLaws}`Monad` should work equivalently to these default implementations.
In other words, a type that provides both {anchorName ApplicativeLaws}`Applicative` and {anchorName ApplicativeLaws}`Monad` instances should not have an implementation of {anchorTerm MonadExtends}`seq` that works differently from the version that the {anchorName MonadSeq}`Monad` instance generates as a default implementation.
This is important because polymorphic functions may be refactored to replace a use of {lit}`>>=` with an equivalent use of {lit}`<*>`, or a use of {lit}`<*>` with an equivalent use of {lit}`>>=`.
This refactoring should not change the meaning of programs that use this code.

This rule explains why {anchorName ValidateAndThen}`Validate.andThen` should not be used to implement {anchorName MonadExtends}`bind` in a {anchorName ApplicativeLaws}`Monad` instance.
On its own, it obeys the monad contract.
However, when it is used to implement {anchorTerm MonadExtends}`seq`, the behavior is not equivalent to {anchorTerm MonadExtends}`seq` itself.
To see where they differ, take the example of two computations, both of which return errors.
Start with an example of a case where two errors should be returned, one from validating a function (which could have just as well resulted from a prior argument to the function), and one from validating an argument:

```anchor counterexample
def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }

def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }
```

Combining them with the version of {lit}`<*>` from {anchorName Validate}`Validate`'s {anchorName ApplicativeValidate}`Applicative` instance results in both errors being reported to the user:
```anchorEvalSteps realSeq
notFun <*> notArg
===>
match notFun with
| .ok g => g <$> notArg
| .errors errs =>
  match notArg with
  | .ok _ => .errors errs
  | .errors errs' => .errors (errs ++ errs')
===>
match notArg with
| .ok _ =>
  .errors { head := "First error", tail := [] }
| .errors errs' =>
  .errors ({ head := "First error", tail := [] } ++ errs')
===>
.errors
  ({ head := "First error", tail := [] } ++
   { head := "Second error", tail := []})
===>
.errors {
  head := "First error",
  tail := ["Second error"]
}
```

Using the version of {anchorName MonadSeqDesugar}`seq` that was implemented with {lit}`>>=`, here rewritten to {anchorName fakeSeq}`andThen`, results in only the first error being available:
```anchorEvalSteps fakeSeq
seq notFun (fun () => notArg)
===>
notFun.andThen fun g =>
notArg.andThen fun y =>
pure (g y)
===>
match notFun with
| .errors errs => .errors errs
| .ok val =>
  (fun g =>
    notArg.andThen fun y =>
    pure (g y)) val
===>
.errors { head := "First error", tail := [] }
```
