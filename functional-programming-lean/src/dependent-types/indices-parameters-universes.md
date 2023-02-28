# Indices, Parameters, and Universe Levels

The distinction between indices and parameters of an inductive type is more than just a way to describe arguments to the type that either vary or do not between the constructors.
Whether an argument to an inductive type is a parameter or an index also matters when it comes time to determine the relationships between their universe levels.
In particular, an inductive type may have the same universe level as a parameter, but it must be in a larger universe than its indices.
This restriction is necessary to ensure that Lean can be used as a theorem prover as well as a programming language.
Experimenting with error messages is a good way to illustrate these rules, as well as the precise rules that determine whether an argument to a type is a parameter or an index.

Generally speaking, the definition of an inductive type takes its parameters before a colon and its indices after the colon.
Parameters are given names like function arguments, whereas indices only have their types described.
This can be seen in the definition of `Vect`:
```lean
{{#example_decl Examples/DependentTypes.lean Vect}}
```
In this definition, `α` is a parameter and the `Nat` is an index.
Parameters may be referred to throughout the definition (for example, `Vect.cons` uses `α` for the type of its first argument), but they must always be used consistently.
Because indices are expected to change, they are assigned individual values at each constructor, rather than being provided as arguments at the top of the datatype definition.


A very simple datatype with a parameter is `WithParameter`:
```lean
{{#example_decl Examples/DependentTypes/IndicesParameters.lean WithParameter}}
```
The universe level `u` can be used for both the parameter and for the inductive type itself, illustrating that parameters do not increase the universe level of a datatype.
Similarly, when there are multiple parameters, the inductive type receives whichever universe level is greater:
```lean
{{#example_decl Examples/DependentTypes/IndicesParameters.lean WithTwoParameters}}
```
Because parameters do not increase the universe level of a datatype, they can be more convenient to work with.
Lean attempts to identify arguments that are described like indices (after the colon), but used like parameters, and turn them into parameters:
Both of the following inductive datatypes have their parameter written after the colon:
```lean
{{#example_decl Examples/DependentTypes/IndicesParameters.lean WithParameterAfterColon}}

{{#example_decl Examples/DependentTypes/IndicesParameters.lean WithParameterAfterColon2}}
```

When a parameter is not named in the initial datatype declaration, different names may be used for it in each constructor, so long as they are used consistently.
The following declaration is accepted:
```lean
{{#example_decl Examples/DependentTypes/IndicesParameters.lean WithParameterAfterColonDifferentNames}}
```
However, this flexibility does not extend to datatypes that explicitly declare the names of their parameters:
```lean
{{#example_in Examples/DependentTypes/IndicesParameters.lean WithParameterBeforeColonDifferentNames}}
```
```output error
{{#example_out Examples/DependentTypes/IndicesParameters.lean WithParameterBeforeColonDifferentNames}}
```
Similarly, attempting to name an index results in an error:
```lean
{{#example_in Examples/DependentTypes/IndicesParameters.lean WithNamedIndex}}
```
```output error
{{#example_out Examples/DependentTypes/IndicesParameters.lean WithNamedIndex}}
```

Using an appropriate universe level and placing the index after the colon results in a declaration that is acceptable:
```lean
{{#example_decl Examples/DependentTypes/IndicesParameters.lean WithIndex}}
```


Even though Lean can sometimes determine that an argument after the colon in an inductive type declaration is a parameter when it is used consistently in all constructors, all parameters are still required to come before all indices.
Attempting to place a parameter after an index results in the argument being considered an index itself, which would require the universe level of the datatype to increase:
```lean
{{#example_in Examples/DependentTypes/IndicesParameters.lean ParamAfterIndex}}
```
```output error
{{#example_out Examples/DependentTypes/IndicesParameters.lean ParamAfterIndex}}
```

Parameters need not be types.
This example shows that ordinary datatypes such as `Nat` may be used as parameters:
```lean
{{#example_in Examples/DependentTypes/IndicesParameters.lean NatParamFour}}
```
```output error
{{#example_out Examples/DependentTypes/IndicesParameters.lean NatParamFour}}
```
Using the `n` as suggested causes the declaration to be accepted:
```lean
{{#example_decl Examples/DependentTypes/IndicesParameters.lean NatParam}}
```




What can be concluded from these experiments?
The rules of parameters and indices are as follows:
 1. Parameters must be used identically in each constructor's type.
 2. All parameters must come before all indices.
 3. The universe level of the datatype being defined must be at least as large as the largest parameter, and strictly larger than the largest index.
 4. Named arguments written before the colon are always parameters, while arguments after the colon are typically indices. Lean may determine that the usage of arguments after the colon makes them into parameters if they are used consistently in all constructors and don't come after any indices.

When in doubt, the Lean command `#print` can be used to check how many of a datatype's arguments are parameters.
For example, for `Vect`, it points out that the number of parameters is 1:
```lean
{{#example_in Examples/DependentTypes/IndicesParameters.lean printVect}}
```
```output info
{{#example_out Examples/DependentTypes/IndicesParameters.lean printVect}}
```

It is worth thinking about which arguments should be parameters and which should be indices when choosing the order of arguments to a datatype.
Having as many arguments as possible be parameters helps keep universe levels under control, which can make a complicated program easier to type check.
One way to make this possible is to ensure that all parameters come before all indices in the argument list.
