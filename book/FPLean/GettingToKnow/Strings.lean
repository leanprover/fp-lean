module
public import VersoManual
import FPLean.Examples



open Verso.Genre Manual
open Verso Code External

open FPLean
example_module Examples.Strings

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Strings"

#doc (Manual) "Characters, Strings, and Slices" =>
%%%
tag := "chars-strings-slices"
%%%

In Lean, strings contain Unicode text.
Specifically, they are sequences of characters, and characters are Unicode code points.
Strings are written in double quotes, and individual characters are written in single quotes.
The type of strings is {anchorName names}`String` and the type of characters is {anchorName names}`Char`.

:::paragraph
Strings can be appended with the {anchorTerm helloWorld}`++` operator:
```anchor helloWorld
#eval "Hello, " ++ "world"
```
```anchorInfo helloWorld
"Hello, world"
```

A character can be added to the end of a string using {anchorName pushExplicit}`String.push`:
```anchor pushExplicit
#eval String.push "Hello" '!'
```
```anchorInfo pushExplicit
"Hello!"
```

This function can also be called using the {ref "behind-the-scenes"}[dot notation] that is used with structure accessors:
```anchor push
#eval "Hello".push '!'
```
```anchorInfo push
"Hello!"
```
:::


# Slices
%%%
tag := "string-slices"
%%%

Strings are represented by their UTF-8 encoding as an array of bytes paired with a cached character count.
This means that removing even a single character from a string can result in copying the remaining characters to a new string.

To allow string-processing code to be written from small, composable pieces, many string operations return {deftech}_string slices_, which are regions of some other string.
String slices have the type {anchorName names}`String.Slice`.
A slice contains a reference to a string along with the start and end positions of the slice, and multiple slices can share the same string.
Operations such as dropping prefixes of strings return slices rather than allocating new strings, and large parts of the string API are also implemented for slices.

Operations that return slices include {anchorName names}`String.trimAscii`, which returns a slice that drops leading and trailing space, tab, newline, and carriage return characters from a string; {anchorName names}`String.drop` and {anchorName names}`String.dropEnd`, which drop the specified number of characters from the start or end of a string; and {anchorName names}`String.dropWhile` and {anchorName names}`String.dropEndWhile`, which respectively remove all the characters that match a pattern from the beginning or end of a string.
The patterns used to search in strings are distinct from those used for {ref "pattern-matching"}[pattern matching]; in the string API, they are function arguments that specify characters or specific substrings to match.
The string slice API includes all the slice-producing string functions as well, which makes it possible to write string manipulations as a series of incremental steps without risking intermediate string copying.

:::paragraph
This code removes characters from the beginning and end of a string without allocating an intermediate string:
```anchor copy
#eval (("small tortoiseshell".drop 6).dropEnd 5).copy
```
```anchorInfo copy
"tortoise"
```
The function {anchorName names}`String.Slice.copy` returns a copy of the region of the underlying string that the slice indicates.
The initial call to {anchorName names}`String.drop` returns a slice, and the call to {anchorName names}`String.Slice.dropEnd` returns an adjusted slice.
The final call to {anchorName copy}`copy` creates a string once more.
:::

Unlike strings, slices do not cache a character count.
Because the UTF-8 encoding of characters may occupy multiple bytes, there's no efficient way to check the length of a string slice.
However, checking whether it is empty can be accomplished with {anchorName names}`String.Slice.isEmpty`.

# Matching
%%%
tag := "string-matching"
%%%


Functions that match parts of strings, such as {anchorName names}`String.dropWhile` and {anchorName names}`String.dropEndWhile`, are overloaded.
They can be called with a variety of different _patterns_, each of which matches substrings in its own way.

:::paragraph
The pattern can be a character, in which case runs of the character are removed:
```anchor dropEndWhileChar
#eval "red admiral".dropEndWhile 'l'
```
```anchorInfo dropEndWhileChar
red admira
```
The output is not in quotes because it is a string slice, and string slices are displayed without surrounding quotes.
The pattern may also be a string, in which case runs of the complete string are removed:
```anchor dropWhileString
#eval "the the butterfly".dropWhile "the "
```
```anchorInfo dropWhileString
butterfly
```
Incomplete matches are not removed:
```anchor dropWhileString2
#eval ("a gray grayling".drop 2).dropWhile "gray "
```
```anchorInfo dropWhileString2
grayling
```
The pattern may also be a function that returns {anchorName names}`true` or {anchorName names}`false`.
Characters are removed until the function returns {anchorName names}`false`.
The slice is converted to a string in order to illustrate that the trailing space remains:
```anchor dropEndWhileFun
#eval ("red admiral".dropEndWhile Char.isAlpha).copy
```
```anchorInfo dropEndWhileFun
"red "
```
:::


# Messages You May Meet
%%%
tag := "string-messages-you-may-meet"
%%%

The overloaded string-matching functions are implemented using features that are explained later in the book, namely {ref "type-classes"}[type classes] and {ref "dependent-types"}[dependent types].
There are two error messages in particular that are useful to learn to read before learning about those features of Lean.

:::paragraph
Calling the functions without a pattern results in an error:
```anchor dropEndWhileNoArg
#eval "red admiral".dropEndWhile
```
```anchorError dropEndWhileNoArg
don't know how to synthesize implicit argument `ρ`
  @String.dropEndWhile ?m.2 "red admiral"
context:
⊢ Type
```
This error is stating that Lean can't determine which pattern type to use, because no pattern was provided.
It can be fixed by providing a pattern.
:::


:::paragraph
When the functions are called with an argument that isn't a valid pattern, there is a compile-time error:
```anchor dropEndWhileListArg
#eval "12345abcde".dropEndWhile [12]
```
```anchorError dropEndWhileListArg
failed to synthesize instance of type class
  String.Slice.Pattern.BackwardPattern [12]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
This error message means that {anchorName names}`String.dropEndWhile` is not overloaded for the pattern {anchorTerm dropEndWhileListArg}`[12]`.
It can be fixed by providing a meaningful pattern, such as a function, character, or string.
:::
