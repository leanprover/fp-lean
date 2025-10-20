import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"


set_option pp.rawOnError true

#doc (Manual) "Summary" =>
%%%
tag :="type-classes-summary"
%%%

# Type Classes and Overloading
%%%
tag := none
%%%

Type classes are Lean's mechanism for overloading functions and operators.
A polymorphic function can be used with multiple types, but it behaves in the same manner no matter which type it is used with.
For example, a polymorphic function that appends two lists can be used no matter the type of the entries in the list, but it is unable to have different behavior depending on which particular type is found.
An operation that is overloaded with type classes, on the other hand, can also be used with multiple types.
However, each type requires its own implementation of the overloaded operation.
This means that the behavior can vary based on which type is provided.

A _type class_ has a name, parameters, and a body that consists of a number of names with types.
The name is a way to refer to the overloaded operations, the parameters determine which aspects of the definitions can be overloaded, and the body provides the names and type signatures of the overloadable operations.
Each overloadable operation is called a {deftech}_method_ of the type class.
Type classes may provide default implementations of some methods in terms of the others, freeing implementors from defining each overload by hand when it is not needed.

An {deftech}_instance_ of a type class provides implementations of the methods for given parameters.
Instances may be polymorphic, in which case they can work for a variety of parameters, and they may optionally provide more specific implementations of default methods in cases where a more efficient version exists for some particular type.

Type class parameters are either {deftech}_input parameters_ (the default), or {deftech}_output parameters_ (indicated by an {moduleName}`outParam` modifier).
Lean will not begin searching for an instance until all input parameters are no longer metavariables, while output parameters may be solved while searching for instances.
Parameters to a type class need not be types—they may also be ordinary values.
The {moduleName}`OfNat` type class, used to overload natural number literals, takes the overloaded {moduleName}`Nat` itself as a parameter, which allows instances to restrict the allowed numbers.

Instances may be marked with a {anchorTerm defaultAdd}`@[default_instance]` attribute.
When an instance is a default instance, then it will be chosen as a fallback when Lean would otherwise fail to find an instance due to the presence of metavariables in the type.

# Type Classes for Common Syntax
%%%
tag := none
%%%

Most infix operators in Lean are overridden with a type class.
For instance, the addition operator corresponds to a type class called {moduleName}`Add`.
Most of these operators have a corresponding heterogeneous version, in which the two arguments need not have the same type.
These heterogeneous operators are overloaded using a version of the class whose name starts with {lit}`H`, such as {moduleName}`HAdd`.

Indexing syntax is overloaded using a type class called {moduleName}`GetElem`, which involves proofs.
{moduleName}`GetElem` has two output parameters, which are the type of elements to be extracted from the collection and a function that can be used to determine what counts as evidence that the index value is in bounds for the collection.
This evidence is described by a proposition, and Lean attempts to prove this proposition when array indexing is used.
When Lean is unable to check that list or array access operations are in bounds at compile time, the check can be deferred to run time by appending a {lit}`?` to the indexing syntax.

# Functors
%%%
tag := none
%%%


A functor is a polymorphic type that supports a mapping operation.
This mapping operation transforms all elements “in place”, changing no other structure.
For instance, lists are functors and the mapping operation may neither drop, duplicate, nor mix up entries in the list.

While functors are defined by having {anchorName FunctorDef}`map`, the {anchorName FunctorDef}`Functor` type class in Lean contains an additional default method that is responsible for mapping the constant function over a value, replacing all values whose type are given by polymorphic type variable with the same new value.
For some functors, this can be done more efficiently than traversing the entire structure.

# Deriving Instances
%%%
tag := none
%%%


Many type classes have very standard implementations.
For instance, the Boolean equality class {moduleName}`BEq` is usually implemented by first checking whether both arguments are built with the same constructor, and then checking whether all their arguments are equal.
Instances for these classes can be created _automatically_.

When defining an inductive type or a structure, a {kw}`deriving` clause at the end of the declaration will cause instances to be created automatically.
Additionally, the {kw}`deriving instance`﻿{lit}` ... `﻿{kw}`for`﻿{lit}` ...` command can be used outside of the definition of a datatype to cause an instance to be generated.
Because each class for which instances can be derived requires special handling, not all classes are derivable.

# Coercions
%%%
tag := none
%%%


Coercions allow Lean to recover from what would normally be a compile-time error by inserting a call to a function that transforms data from one type to another.
For example, the coercion from any type {anchorName CoeOption}`α` to the type {anchorTerm CoeOption}`Option α` allows values to be written directly, rather than with the {anchorName CoeOption}`some` constructor, making {anchorName CoeOption}`Option` work more like nullable types from object-oriented languages.

There are multiple kinds of coercion.
They can recover from different kinds of errors, and they are represented by their own type classes.
The {anchorName CoeOption}`Coe` class is used to recover from type errors.
When Lean has an expression of type {anchorName Coe}`α` in a context that expects something with type {anchorName Coe}`β`, Lean first attempts to string together a chain of coercions that can transform {anchorName Coe}`α`s into {anchorName Coe}`β`s, and only displays the error when this cannot be done.
The {moduleName}`CoeDep` class takes the specific value being coerced as an extra parameter, allowing either further type class search to be done on the value or allowing constructors to be used in the instance to limit the scope of the conversion.
The {moduleName}`CoeFun` class intercepts what would otherwise be a “not a function” error when compiling a function application, and allows the value in the function position to be transformed into an actual function if possible.
