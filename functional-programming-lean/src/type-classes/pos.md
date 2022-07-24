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
Lean's built-in addition operator relies on a class named `Add` that is almost identical to `Plus`.
When a programmer writes `{{#example_eval Examples/Classes.lean plusDesugar 0}}`, it is interpreted as meaning `{{#example_eval Examples/Classes.lean plusDesugar 1}}`.
Defining an instance of `Add Pos` allows `Pos` values to use ordinary addition syntax:
```Lean
{{#example_decl Examples/Classes.lean AddPos}}

{{#example_decl Examples/Classes.lean betterFourteen}}
```

Another useful built-in class is called `ToString`.
Instances of `ToString` provide a standard way of converting a type to a string.
For instance, a `ToString` instance is used when a value occurs in an interpolated string, and it determines how the `IO.println` function used at the [beginning of the description of `IO`](../hello-world/running-a-program.html#running-a-program) will display a value.

For example, one way to convert a `Pos` into a `String` is to reveal its inner structure.
The function `posToString` takes a `Bool` that determines whether to parenthesize uses of `Pos.succ`---this should be `true` in the initial call to the function, and `false` in all recursive calls.
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

## Instance Implicits

It can be useful to write functions that work for _any_ overloading of a given function.
For instance, `IO.println` works for any type that has an instance of `ToString`.
This is indicated using square brackets around the required instance.
For example, the type of `IO.println` is `{{#example_out Examples/Classes.lean printlnType}}`.
This type says that `IO.println` accepts an argument of type `α`, which Lean should determine automatically, and that there must be a `ToString` instance available for `α`.
It returns an `IO` action.


This can be accomplished using _instance implicits_.

Thus far, there have been two kinds of function arguments:

 * Explicit arguments, which are to be provided by the caller of the function
 * Implicit arguments, which are found by Lean when a unique type-correct solution exists
 
Implicit arguments are surrounded with curly braces (`{` and `}`) in a function's type.





