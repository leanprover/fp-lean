# Overloading and Type Classes

In many languages, the built-in datatypes get special treatment.
For example, in C and Java, `+` can be used to add `float`s and `int`s, but not arbitrary-precision numbers from a third-party library.
Similarly, numeric literals can be used directly for the built-in types, but not for user-defined number types.
Other languages provide an _overloading_ mechanism for operators, where the same operator can be given a meaning for a new type.
In these languages, such as C++ and C#, a wide variety of built-in operators can be overloaded, and the compiler uses the type checker to select a particular implementation.

In addition to numeric literals and operators, many languages allow overloading of functions or methods.
In C++, Java, C# and Kotlin, multiple implementations of a method are allowed, with differing numbers and types of arguments.
The compiler uses the number of arguments and their types to determine which overload was intended.

Function and operator overloading has a key limitation: polymorphic functions can't restrict their type arguments to types for which a given overload exists.
For example, an overloaded method might be defined for strings, byte arrays, and file pointers, but there's no way to write a second method that works for any of these.
Instead, this second method must itself be overloaded for each type that has an overload of the original method, resulting in many boilerplate definitions instead of a single polymorphic definition.
Another consequence of this restriction is that some operators (such as equality in Java) end up being defined for _every_ combination of arguments, even when it is not necessarily sensible to do so.
If programmers are not very careful, this can lead to programs that crash at runtime or silently compute an incorrect result.

Lean implements overloading using a mechanism called _type classes_, pioneered in Haskell, that allows overloading of operators, functions, and literals in a manner that works well with polymorphism.
A type class describes a collection of overloadable operations.
To overload these operations for a new type, an _instance_ is created that contains an implementation of each operation for the new type.
For example, a type class named `Add` describes types that allow addition, and an instance of `Add` for `Nat` provides an implementation of addition for `Nat`.

The terms _class_ and _instance_ can be confusing for those who are used to object-oriented languages, because they are not closely related to classes and instances in object-oriented languages.
However, they do share common roots: in everyday language, the term "class" refers to a group that shares some common attributes.
While classes in object-oriented programming certainly describe groups of objects with common attributes, the term additionally refers to a specific mechanism in a programming language for describing such a group.
Type classes are also a means of describing types that share common attributes (namely, implementations of certain operations), but they don't really have anything else in common with classes as found in object-oriented programming.

A Lean type class is much more analogous to a Java or C# _interface_.
Both type classes and interfaces describe a conceptually related set of operations that are implemented for a type or collection of types.
Similarly, an instance of a type class is akin to the code in a Java or C# class that is prescribed by the implemented interfaces, rather than an instance of a Java or C# class.
Unlike Java or C#'s interfaces, types can be given instances for type classes that the author of the type does not have access to.
In this way, they are very similar to Rust traits.





