import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.InsertionSort"

#doc (Manual) "Summary" =>
%%%
tag := "programs-proofs-summary"
%%%

# Tail Recursion
%%%
tag := none
%%%

Tail recursion is recursion in which the results of recursive calls are returned immediately, rather than being used in some other way.
These recursive calls are called _tail calls_.
Tail calls are interesting because they can be compiled to a jump instruction rather than a call instruction, and the current stack frame can be re-used instead of pushing a new frame.
In other words, tail-recursive functions are actually loops.

A common way to make a recursive function faster is to rewrite it in accumulator-passing style.
Instead of using the call stack to remember what is to be done with the result of a recursive call, an additional argument called an _accumulator_ is used to collect this information.
For example, an accumulator for a tail-recursive function that reverses a list contains the already-seen list entries, in reverse order.

In Lean, only self-tail-calls are optimized into loops.
In other words, two functions that each end with a tail call to the other will not be optimized.

# Reference Counting and In-Place Updates
%%%
tag := none
%%%

Rather than using a tracing garbage collector, as is done in Java, C#, and most JavaScript implementations, Lean uses reference counting for memory management.
This means that each value in memory contains a field that tracks how many other values refer to it, and the run-time system maintains these counts as references appear or disappear.
Reference counting is also used in Python, PHP, and Swift.

When asked to allocate a fresh object, Lean's run-time system is able to recycle existing objects whose reference counts are falling to zero.
Additionally, array operations such as {anchorName names}`Array.set` and {anchorName names}`Array.swap` will mutate an array if its reference count is one, rather than allocating a modified copy.
If {anchorName names}`Array.swap` holds the only reference to an array, then no other part of the program can tell that it was mutated rather than copied.

Writing efficient code in Lean requires the use of tail recursion and being careful to ensure that large arrays are used uniquely.
While tail calls can be identified by inspecting the function's definition, understanding whether a value is referred to uniquely may require reading the whole program.
The debugging helper {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared` can be used at key locations in the program to check that a value is not shared.

# Proving Programs Correct
%%%
tag := none
%%%

Rewriting a program in accumulator-passing style, or making other transformations that make it run faster, can also make it more difficult to understand.
It can be useful to keep the original version of the program that is more clearly correct, and then use it as an executable specification for the optimized version.
While techniques such as unit testing work just as well in Lean as in any other language, Lean also enables the use of mathematical proofs that completely ensure that both versions of the function return the same result for _all possible_ inputs.

Typically, proving that two functions are equal is done using function extensionality (the {kw}`funext` tactic), which is the principle that two functions are equal if they return the same values for every input.
If the functions are recursive, then induction is usually a good way to prove that their outputs are the same.
Usually, the recursive definition of the function will make recursive calls on one particular argument; this argument is a good choice for induction.
In some cases, the induction hypothesis is not strong enough.
Fixing this problem usually requires thought about how to construct a more general version of the theorem statement that provides induction hypotheses that are strong enough.
In particular, to prove that a function is equivalent to an accumulator-passing version, a theorem statement that relates arbitrary initial accumulator values to the final result of the original function is needed.

# Safe Array Indices
%%%
tag := none
%%%

The type {anchorTerm names}`Fin n` represents natural numbers that are strictly less than {anchorName names}`n`.
{anchorName names}`Fin` is short for “finite”.
As with subtypes, a {anchorTerm names}`Fin n` is a structure that contains a {anchorName names}`Nat` and a proof that this {anchorName names}`Nat` is less than {anchorName names}`n`.
There are no values of type {anchorTerm names}`Fin 0`.

If {anchorName names}`arr` is an {anchorTerm names}`Array α`, then {anchorTerm names}`Fin arr.size` always contains a number that is a suitable index into {anchorName names}`arr`.

Lean provides instances of most of the useful numeric type classes for {anchorName names}`Fin`.
The {anchorName names}`OfNat` instances for {anchorName names}`Fin` perform modular arithmetic rather than failing at compile time if the number provided is larger than the {anchorName names}`Fin` can accept.

# Provisional Proofs
%%%
tag := none
%%%

Sometimes, it can be useful to pretend that a statement is proved without actually doing the work of proving it.
This can be useful when making sure that a proof of a statement would be suitable for some task, such as a rewrite in another proof, determining that an array access is safe, or showing that a recursive call is made on a smaller value than the original argument.
It's very frustrating to spend time proving something, only to discover that some other proof would have been more useful.

The {anchorTerm names}`sorry` tactic causes Lean to provisionally accept a statement as if it were a real proof.
It can be seen as analogous to a stub method that throws a {CSharp}`NotImplementedException` in C#.
Any proof that relies on {anchorTerm names}`sorry` includes a warning in Lean.

Be careful!
The {anchorTerm names}`sorry` tactic can prove _any_ statement, even false statements.
Proving that {anchorTerm names}`3 < 2` can cause an out-of-bounds array access to persist to runtime, unexpectedly crashing a program.
Using {anchorTerm names}`sorry` is convenient during development, but keeping it in the code is dangerous.

# Proving Termination
%%%
tag := none
%%%

When a recursive function does not use structural recursion, Lean cannot automatically determine that it terminates.
In these situations, the function could just be marked {kw}`partial`.
However, it is also possible to provide a proof that the function terminates.

Partial functions have a key downside: they can't be unfolded during type checking or in proofs.
This means that Lean's value as an interactive theorem prover can't be applied to them.
Additionally, showing that a function that is expected to terminate actually always does terminate removes one more potential source of bugs.

The {kw}`termination_by` clause that's allowed at the end of a function can be used to specify the reason why a recursive function terminates.
The clause maps the function's arguments to an expression that is expected to be smaller for each recursive call.
Some examples of expressions that might decrease are the difference between a growing index into an array and the array's size, the length of a list that's cut in half at each recursive call, or a pair of lists, exactly one of which shrinks on each recursive call.

Lean contains proof automation that can automatically determine that some expressions shrink with each call, but many interesting programs will require manual proofs.
These proofs can be provided with {kw}`have`, a version of {kw}`let` that's intended for locally providing proofs rather than values.

A good way to write recursive functions is to begin by declaring them {kw}`partial` and debugging them with testing until they return the right answers.
Then, {kw}`partial` can be removed and replaced with a {kw}`termination_by` clause.
Lean will place error highlights on each recursive call for which a proof is needed that contains the statement that needs to be proved.
Each of these statements can be placed in a {kw}`have`, with the proof being {anchorTerm names}`sorry`.
If Lean accepts the program and it still passes its tests, the final step is to actually prove the theorems that enable Lean to accept it.
This approach can prevent wasting time on proving that a buggy program terminates.
