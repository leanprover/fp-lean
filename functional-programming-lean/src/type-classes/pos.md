# Positive Numbers

In some applications, only positive numbers make sense.
For instance, programming languages typically use one-indexed line and column numbers for source positions.
Rather than relying on natural numbers, and littering the code with assertions that the number is not zero, it can be useful to design a datatype that represents only positive numbers.

One way to represent positive numbers is very similar to `Nat`, except with `one` as the base case instead of `zero`:
```Lean
{{#example_decl Examples/Classes.lean Pos}}
```
This datatype represents exactly the intended set of values, but it is not very convenient to use.
For instance, numeric literals are rejected:
```Lean
{{#example_in Examples/Classes.lean sevenOops}}
```
```Lean error
{{#example_out Examples/Classes.lean sevenOops}}
```
Instead, the constructors must be used directly:
```Lean
{{#example_decl Examples/Classes.lean seven}}
```

Similarly, addition and multiplication are not easy to use:
```Lean
{{#example_in Examples/Classes.lean fourteenOops}}
```
```Lean error
{{#example_out Examples/Classes.lean fourteenOops}}
```
```Lean
{{#example_in Examples/Classes.lean fortyNineOops}}
```
```Lean error
{{#example_out Examples/Classes.lean fortyNineOops}}
```

Each of these error messages begins with `failed to synthesize instance`.
This indicates that the error is due to an overloaded operation that has not been implemented, and it describes the type class that must be implemented.

## Classes and Instances

A type class consists of a name, some arguments, and a collection of _methods_.
Once again, there is a terminology clash with object oriented languages.
In object oriented languages, a method is essentially a function that is connected to a particular object in memory, with special access to the object's private state.
Objects are interacted with via their methods.
In languages with type classes, the term "method" refers to an operation that has been declared to be overloadable, and has no special connection to objects or values or private fields.

In the following, `Plus` is the name of the class, `α : Type` is the only argument, and `plus : α → α → α` is the method:
```Lean
{{#example_decl Examples/Classes.lean Plus}}
```
This declaration says that there is a type class `Plus` that overloads operations with respect to a type `α`.
In particular, there is one overloaded operation called `plus`, that takes two `α`s and returns an `α`.

Type classes are first class, just as types are first class.
This means that they can be defined using `def`, passed as arguments to functions, and that they have types themselves.
In particular, a type class is another kind of type.
The type of `{{#example_in Examples/Classes.lean PlusType}}` is `{{#example_out Examples/Classes.lean PlusType}}`, because it takes a type as an argument (`α`) and results in a new type that describes the overloading of `Plus`'s operation for `α`.


To overload `plus` for a particular type, write an instance:
```Lean
{{#example_decl Examples/Classes.lean PlusNat}}
```
The colon after `instance` indicates that `Plus Nat` is indeed a type.
Each method of class `Plus` should be assigned a value using `:=`.
In this case, there is only one method: `plus`.

After this overloaded operation has been declared, it becomes possible to use it with natural numbers:
```Lean
{{#example_in Examples/Classes.lean plusNatFiveThree}}
```
```Lean info
{{#example_out Examples/Classes.lean plusNatFiveThree}}
```
By default, type class methods are defined in a namespace with the same name as the type class.
It can be convenient to `open` the namespace so that users don't need to type the name of the class first.
Parentheses in an `open` command indicate that only the indicated names from the namespace are to be made accessible:
```Lean
{{#example_decl Examples/Classes.lean openPlus}}

{{#example_in Examples/Classes.lean plusNatFiveThreeAgain}}
```
```Lean info
{{#example_out Examples/Classes.lean plusNatFiveThreeAgain}}
```

Defining an addition function for `Pos` and an instance of `Plus Pos` allows `Pos` and `Nat` to use the same addition function:
```Lean
{{#example_decl Examples/Classes.lean PlusPos}}
```

## Overloaded Addition
Lean's built-in addition operator relies on a class named `Add` that is almost identical to `Plus`.
When a programmer writes `{{#example_eval Examples/Classes.lean plusDesugar 0}}`, it is interpreted as meaning `{{#example_eval Examples/Classes.lean plusDesugar 1}}`.
Defining an instance of `Add Pos` allows `Pos` values to use ordinary addition syntax:
```Lean
{{#example_decl Examples/Classes.lean AddPos}}

{{#example_decl Examples/Classes.lean betterFourteen}}
```

## Conversion to Strings

Another useful built-in class is called `ToString`.
Instances of `ToString` provide a standard way of converting a type to a string.
For instance, a `ToString` instance is used when a value occurs in an interpolated string, and it determines how the `IO.println` function used at the [beginning of the description of `IO`](../hello-world/running-a-program.html#running-a-program) will display a value.

For example, one way to convert a `Pos` into a `String` is to reveal its inner structure.
The function `posToString` takes a `Bool` that determines whether to parenthesize uses of `Pos.succ`—this should be `true` in the initial call to the function, and `false` in all recursive calls.
```Lean
{{#example_decl Examples/Classes.lean posToStringStructure}}
```
Using this function for a `ToString` instance:
```Lean
{{#example_decl Examples/Classes.lean UglyToStringPos}}
```
results in informative, yet overwhelming, output:
```Lean
{{#example_in Examples/Classes.lean sevenLong}}
```
```Lean info
{{#example_out Examples/Classes.lean sevenLong}}
```

On the other hand, every positive number has a corresponding `Nat`.
Converting it to a `Nat` and then using the `ToString Nat` instance (that is, the overloading of `toString` for `Nat`) is a quick way to generate much shorter output:
```Lean
{{#example_decl Examples/Classes.lean posToNat}}

{{#example_decl Examples/Classes.lean PosToStringNat}}

{{#example_in Examples/Classes.lean sevenShort}}
```
```Lean info
{{#example_out Examples/Classes.lean sevenShort}}
```
When more than one instance is defined, the most recent takes precedence.
Additionally, if a type has a `ToString` instance, then it can be used to display the result of `#eval` even if the type in question was not defined with `deriving Repr`, so `{{#example_in Examples/Classes.lean sevenEvalStr}}` outputs `{{#example_out Examples/Classes.lean sevenEvalStr}}`.

## Overloaded Multiplication

For multiplication, there is a type class called `Mul`.
Just as `{{#example_eval Examples/Classes.lean plusDesugar 0}}` is interpreted as `{{#example_eval Examples/Classes.lean plusDesugar 1}}`, `{{#example_eval Examples/Classes.lean timesDesugar 0}}` is interpreted as `{{#example_eval Examples/Classes.lean timesDesugar 1}}`.
An instance of `Mul` allows ordinary multiplication syntax to be used with `Pos`:
```Lean
{{#example_decl Examples/Classes.lean PosMul}}
```
With this instance, multiplication works as expected:
```Lean
{{#example_in Examples/Classes.lean muls}}
```
```Lean info
{{#example_out Examples/Classes.lean muls}}
```

## Literal Numbers

It is quite inconvenient to write out a sequence of constructors for positive numbers.
One way to work around the problem would be to provide a function to convert a `Nat` into a `Pos`.
However, this approach has downsides.
First off, because `Pos` cannot represent `0`, the resulting function would either convert a `Nat` to a bigger number, or it would return `Option Nat`.
Neither is particularly convenient.
Secondly, the need to call the function explicitly would make programs that use positive numbers much less convenient to write than programs that use `Nat`.
Having a trade-off between precise types and convenient APIs means that the precise types become less useful.

In Lean, natural number literals are interpreted using a type class called `OfNat`:
```Lean
{{#example_decl Examples/Classes.lean OfNat}}
```
This type class takes two arguments: `α` is the type for which a natural number is overloaded, and the unnamed `Nat` argument is the actual literal number that was encountered in the program.
Because the class contains the `Nat` argument, it becomes possible to define only instances for those values where the number makes sense.

For example, a sum type that represents natural numbers less than four can be defined as follows:
```Lean
{{#example_decl Examples/Classes.lean LT4}}
```
While it would not make sense to allow _any_ literal number to be used for this type, numbers less than four clearly make sense:


## Exercises

Replace the definition of `Pos` with the following structure:



