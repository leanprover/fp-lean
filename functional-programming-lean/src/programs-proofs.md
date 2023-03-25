# Programming and Proving

This chapter is about programming.
Programs need to compute the correct result, but they also need to do so efficiently.
To write efficient functional programs, it's important to know both how to use data structures appropriately and how to think about the time and space needed to run a program.

This chapter is also about proofs.
One of the most important data structures for efficient programming in Lean is the array, but safe use of arrays requires proving that array indices are in bounds.
Furthermore, most interesting algorithms on arrays do not follow the pattern of structural recursion—instead, they iterate over the array.
While these algorithms terminate, Lean will not necessarily be able to automatically check this.
Proofs can be used to demonstrate why a program terminates.

Combining proofs and programming allows programs to be both safe and efficient.

## Tail Recursion




## Insertion Sort

First show insertion sort. A few proofs needed for array indexing.

Tail recursion

Fin

Reference counting and mutability

Termination by `sorry` - not so great. Let's fix it!

## Inductively Defined Propositions

## Less Than on Nat
