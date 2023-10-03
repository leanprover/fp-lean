# Positive Numbers

In some applications, only positive numbers make sense.
For example, compilers and interpreters typically use one-indexed line and column numbers for source positions, and a datatype that represents only non-empty lists will never report a length of zero.
Rather than relying on natural numbers, and littering the code with assertions that the number is not zero, it can be useful to design a datatype that represents only positive numbers.

One way to represent positive numbers is very similar to `Nat`, except with `one` as the base case instead of `zero`:
```lean
{{#example_decl Examples/Classes.lean Pos}}
```
This datatype represents exactly the intended set of values, but it is not very convenient to use.
For example, numeric literals are rejected:
```lean
{{#example_in Examples/Classes.lean sevenOops}}
```
```output error
{{#example_out Examples/Classes.lean sevenOops}}
```
Instead, the constructors must be used directly:
```lean
{{#example_decl Examples/Classes.lean seven}}
```

Similarly, addition and multiplication are not easy to use:
```lean
{{#example_in Examples/Classes.lean fourteenOops}}
```
```output error
{{#example_out Examples/Classes.lean fourteenOops}}
```
```lean
{{#example_in Examples/Classes.lean fortyNineOops}}
```
```output error
{{#example_out Examples/Classes.lean fortyNineOops}}
```

Each of these error messages begins with `failed to synthesize instance`.
This indicates that the error is due to an overloaded operation that has not been implemented, and it describes the type class that must be implemented.

## Classes and Instances

A type class consists of a name, some parameters, and a collection of _methods_.
The parameters describe the types for which overloadable operations are being defined, and the methods are the names and type signatures of the overloadable operations.
Once again, there is a terminology clash with object-oriented languages.
In object-oriented programming, a method is essentially a function that is connected to a particular object in memory, with special access to the object's private state.
Objects are interacted with via their methods.
In Lean, the term "method" refers to an operation that has been declared to be overloadable, with no special connection to objects or values or private fields.

One way to overload addition is to define a type class named `Plus`, with an addition method named `plus`.
Once an instance of `Plus` for `Nat` has been defined, it becomes possible to add two `Nat`s using `Plus.plus`:
```lean
{{#example_in Examples/Classes.lean plusNatFiveThree}}
```
```output info
{{#example_out Examples/Classes.lean plusNatFiveThree}}
```
Adding more instances allows `Plus.plus` to take more types of arguments.

In the following type class declaration, `Plus` is the name of the class, `α : Type` is the only argument, and `plus : α → α → α` is the only method:
```lean
{{#example_decl Examples/Classes.lean Plus}}
```
This declaration says that there is a type class `Plus` that overloads operations with respect to a type `α`.
In particular, there is one overloaded operation called `plus` that takes two `α`s and returns an `α`.

Type classes are first class, just as types are first class.
In particular, a type class is another kind of type.
The type of `{{#example_in Examples/Classes.lean PlusType}}` is `{{#example_out Examples/Classes.lean PlusType}}`, because it takes a type as an argument (`α`) and results in a new type that describes the overloading of `Plus`'s operation for `α`.


To overload `plus` for a particular type, write an instance:
```lean
{{#example_decl Examples/Classes.lean PlusNat}}
```
The colon after `instance` indicates that `Plus Nat` is indeed a type.
Each method of class `Plus` should be assigned a value using `:=`.
In this case, there is only one method: `plus`.

By default, type class methods are defined in a namespace with the same name as the type class.
It can be convenient to `open` the namespace so that users don't need to type the name of the class first.
Parentheses in an `open` command indicate that only the indicated names from the namespace are to be made accessible:
```lean
{{#example_decl Examples/Classes.lean openPlus}}

{{#example_in Examples/Classes.lean plusNatFiveThreeAgain}}
```
```output info
{{#example_out Examples/Classes.lean plusNatFiveThreeAgain}}
```

Defining an addition function for `Pos` and an instance of `Plus Pos` allows `plus` to be used to add both `Pos` and `Nat` values:
```lean
{{#example_decl Examples/Classes.lean PlusPos}}
```

Because there is not yet an instance of `Plus Float`, attempting to add two floating-point numbers with `plus` fails with a familiar message:
```lean
{{#example_in Examples/Classes.lean plusFloatFail}}
```
```output error
{{#example_out Examples/Classes.lean plusFloatFail}}
```
These errors mean that Lean was unable to find an instance for a given type class.

## Overloaded Addition

Lean's built-in addition operator is syntactic sugar for a type class called `HAdd`, which flexibly allows the arguments to addition to have different types.
`HAdd` is short for _heterogeneous addition_.
For example, an `HAdd` instance can be written to allow a `Nat` to be added to a `Float`, resulting in a new `Float`.
When a programmer writes `{{#example_eval Examples/Classes.lean plusDesugar 0}}`, it is interpreted as meaning `{{#example_eval Examples/Classes.lean plusDesugar 1}}`.

While an understanding of the full generality of `HAdd` relies on features that are discussed in [another section in this chapter](out-params.md), there is a simpler type class called `Add` that does not allow the types of the arguments to be mixed.
The Lean libraries are set up so that an instance of `Add` will be found when searching for an instance of `HAdd` in which both arguments have the same type.

Defining an instance of `Add Pos` allows `Pos` values to use ordinary addition syntax:
```lean
{{#example_decl Examples/Classes.lean AddPos}}

{{#example_decl Examples/Classes.lean betterFourteen}}
```

## Conversion to Strings

Another useful built-in class is called `ToString`.
Instances of `ToString` provide a standard way of converting values from a given type into strings.
For example, a `ToString` instance is used when a value occurs in an interpolated string, and it determines how the `IO.println` function used at the [beginning of the description of `IO`](../hello-world/running-a-program.html#running-a-program) will display a value.

For example, one way to convert a `Pos` into a `String` is to reveal its inner structure.
The function `posToString` takes a `Bool` that determines whether to parenthesize uses of `Pos.succ`, which should be `true` in the initial call to the function and `false` in all recursive calls.
```lean
{{#example_decl Examples/Classes.lean posToStringStructure}}
```
Using this function for a `ToString` instance:
```lean
{{#example_decl Examples/Classes.lean UglyToStringPos}}
```
results in informative, yet overwhelming, output:
```lean
{{#example_in Examples/Classes.lean sevenLong}}
```
```output info
{{#example_out Examples/Classes.lean sevenLong}}
```

On the other hand, every positive number has a corresponding `Nat`.
Converting it to a `Nat` and then using the `ToString Nat` instance (that is, the overloading of `toString` for `Nat`) is a quick way to generate much shorter output:
```lean
{{#example_decl Examples/Classes.lean posToNat}}

{{#example_decl Examples/Classes.lean PosToStringNat}}

{{#example_in Examples/Classes.lean sevenShort}}
```
```output info
{{#example_out Examples/Classes.lean sevenShort}}
```
When more than one instance is defined, the most recent takes precedence.
Additionally, if a type has a `ToString` instance, then it can be used to display the result of `#eval` even if the type in question was not defined with `deriving Repr`, so `{{#example_in Examples/Classes.lean sevenEvalStr}}` outputs `{{#example_out Examples/Classes.lean sevenEvalStr}}`.

## Overloaded Multiplication

For multiplication, there is a type class called `HMul` that allows mixed argument types, just like `HAdd`.
Just as `{{#example_eval Examples/Classes.lean plusDesugar 0}}` is interpreted as `{{#example_eval Examples/Classes.lean plusDesugar 1}}`, `{{#example_eval Examples/Classes.lean timesDesugar 0}}` is interpreted as `{{#example_eval Examples/Classes.lean timesDesugar 1}}`.
For the common case of multiplication of two arguments with the same type, a `Mul` instance suffices.

An instance of `Mul` allows ordinary multiplication syntax to be used with `Pos`:
```lean
{{#example_decl Examples/Classes.lean PosMul}}
```
With this instance, multiplication works as expected:
```lean
{{#example_in Examples/Classes.lean muls}}
```
```output info
{{#example_out Examples/Classes.lean muls}}
```

## Literal Numbers

It is quite inconvenient to write out a sequence of constructors for positive numbers.
One way to work around the problem would be to provide a function to convert a `Nat` into a `Pos`.
However, this approach has downsides.
First off, because `Pos` cannot represent `0`, the resulting function would either convert a `Nat` to a bigger number, or it would return `Option Pos`.
Neither is particularly convenient for users.
Secondly, the need to call the function explicitly would make programs that use positive numbers much less convenient to write than programs that use `Nat`.
Having a trade-off between precise types and convenient APIs means that the precise types become less useful.

In Lean, natural number literals are interpreted using a type class called `OfNat`:
```lean
{{#example_decl Examples/Classes.lean OfNat}}
```
This type class takes two arguments: `α` is the type for which a natural number is overloaded, and the unnamed `Nat` argument is the actual literal number that was encountered in the program.
The method `ofNat` is then used as the value of the numeric literal.
Because the class contains the `Nat` argument, it becomes possible to define only instances for those values where the number makes sense.

`OfNat` demonstrates that the arguments to type classes do not need to be types.
Because types in Lean are first-class participants in the language that can be passed as arguments to functions and given definitions with `def` and `abbrev`, there is no barrier that prevents non-type arguments in positions where a less-flexible language could not permit them.
This flexibility allows overloaded operations to be provided for particular values as well as particular types.

For example, a sum type that represents natural numbers less than four can be defined as follows:
```lean
{{#example_decl Examples/Classes.lean LT4}}
```
While it would not make sense to allow _any_ literal number to be used for this type, numbers less than four clearly make sense:
```lean
{{#example_decl Examples/Classes.lean LT4ofNat}}
```
With these instances, the following examples work:
```lean
{{#example_in Examples/Classes.lean LT4three}}
```
```output info
{{#example_out Examples/Classes.lean LT4three}}
```
```lean
{{#example_in Examples/Classes.lean LT4zero}}
```
```output info
{{#example_out Examples/Classes.lean LT4zero}}
```
On the other hand, out-of-bounds literals are still not allowed:
```lean
{{#example_in Examples/Classes.lean LT4four}}
```
```output error
{{#example_out Examples/Classes.lean LT4four}}
```

For `Pos`, the `OfNat` instance should work for _any_ `Nat` other than `Nat.zero`.
Another way to phrase this is to say that for all natural numbers `n`, the instance should work for `n + 1`.
Just as names like `α` automatically become implicit arguments to functions that Lean fills out on its own, instances can take automatic implicit arguments.
In this instance, the argument `n` stands for any `Nat`, and the instance is defined for a `Nat` that's one greater:
```lean
{{#example_decl Examples/Classes.lean OfNatPos}}
```
Because `n` stands for a `Nat` that's one less than what the user wrote, the helper function `natPlusOne` returns a `Pos` that's one greater than its argument.
This makes it possible to use natural number literals for positive numbers, but not for zero:
```lean
{{#example_decl Examples/Classes.lean eight}}

{{#example_in Examples/Classes.lean zeroBad}}
```
```output error
{{#example_out Examples/Classes.lean zeroBad}}
```

## Exercises

### Another Representation

An alternative way to represent a positive number is as the successor of some `Nat`.
Replace the definition of `Pos` with a structure whose constructor is named `succ` that contains a `Nat`:
```lean
{{#example_decl Examples/Classes.lean AltPos}}
```
Define instances of `Add`, `Mul`, `ToString`, and `OfNat` that allow this version of `Pos` to be used conveniently.

### Even Numbers

Define a datatype that represents only even numbers. Define instances of `Add`, `Mul`, and `ToString` that allow it to be used conveniently.
`OfNat` requires a feature that is introduced in [the next section](polymorphism.md).

### HTTP Requests

An HTTP request begins with an identification of a HTTP method, such as `GET` or `POST`, along with a URI and an HTTP version.
Define an inductive type that represents an interesting subset of the HTTP methods, and a structure that represents HTTP responses.
Responses should have a `ToString` instance that makes it possible to debug them.
Use a type class to associate different `IO` actions with each HTTP method, and write a test harness as an `IO` action that calls each method and prints the result.
