# Type Classes and Polymorphism

It can be useful to write functions that work for _any_ overloading of a given function.
For instance, `IO.println` works for any type that has an instance of `ToString`.
This is indicated using square brackets around the required instance: the type of `IO.println` is `{{#example_out Examples/Classes.lean printlnType}}`.
This type says that `IO.println` accepts an argument of type `α`, which Lean should determine automatically, and that there must be a `ToString` instance available for `α`.
It returns an `IO` action.

Similarly, a function that sums all elements of a list 

This can be accomplished using _instance implicits_.

Thus far, there have been two kinds of function arguments:

 * Explicit arguments, which are to be provided by the caller of the function
 * Implicit arguments, which are found by Lean when a unique type-correct solution exists
 
Implicit arguments are surrounded with curly braces (`{` and `}`) in a function's type.


