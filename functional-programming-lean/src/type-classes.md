# Overloading and Type Classes

In many languages, the built-in datatypes get special treatment.
For instance, in C and Java, `+` can be used to add floats and ints, but not arbitrary-precision numbers included with a library.
Similarly, numeric literals can be used directly for the built-in types, but not for user-defined number types.
Other languages provide an _overloading_ mechanism for operators, where the same operator can be given a meaning for a new type.
In these languages, such as C++ and C#, a wide variety of built-in operators can be overloaded, and the compiler uses the type checker to select a particular implementation.

In addition to numeric literals and operators, many languages allow overloading of functions or methods.
For instance, in C++, Java, C# and Kotlin, multiple implementations of a method are allowed, with differing numbers and types of arguments.
The compiler uses the number of arguments and their type to determine which overload was intended.

Function and operator overloading has a key limitation: polymorphic functions can't restrict their type arguments to types for which a given overload exists.
That is, there is no way to write a function that works for any type that has addition defined.
Instead, this function must itself be overloaded for each type that has addition, resulting in many boilerplate definitions instead of a single polymorphic definition.
Another consequence of this restriction is that some operators (such as equality) end up being defined for _every_ combination of arguments, even when it is not necessarily sensible to do so.
If programmers are not very careful, this can lead to programs that crash at runtime or silently compute an incorrect result.

Lean implements overloading using a mechanism called _type classes_, pioneered in Haskell, that allows overloading of operators, functions, and literals in a manner that works well with polymorphism.
A type class describes a collection of overloadable operations.
To overload these operations for a new type, an _instance_ is created that contains an implementation of each operation for the new type.
For instance, a type class named `Add` describes types that allow addition, and an instance of `Add` for `Nat` provides an implementation of addition for `Nat`.

Type classes and instances in Lean are not closely related to classes in object oriented languages.
In everyday language, the term "class" refers to a group that shares some common attributes.
While classes in object oriented programming certainly describe groups of objects with common attributes, the term additionally refers to a specific mechanism in a programming language for describing such a group.
Type classes are also a means of describing types that share common attributes (namely, implementations of certain operations), but they don't really have anything else in common with classes as found in object oriented programming.
A Lean type class is much more analogous to an interface.
Similarly, instances of type classes describe how to implement a given interface for a type, while the term is used to describe values with a given type in object oriented programming.



TODO:

 * GetElem type class for a[i]
 * Coercions and outparams
