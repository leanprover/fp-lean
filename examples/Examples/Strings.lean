import ExampleSupport

--ANCHOR: names
example := String.Slice.copy
example := String.drop
example := String.dropEnd
example : String → Char → String.Slice := fun s c => String.dropWhile s c
example : String → Char → String.Slice := fun s c => String.dropEndWhile s c
example : String.Slice → Nat → String.Slice := fun s n => String.Slice.dropEnd s n
example := String.trimAscii
example := String.trimAsciiStart
example := String.trimAsciiEnd
example := [String, Char, String.Slice]
example := String.Slice.isEmpty
example := [true, false]
--ANCHOR_END: names

--ANCHOR: helloWorld
#eval "Hello, " ++ "world"
--ANCHOR_END: helloWorld

--ANCHOR: pushExplicit
#eval String.push "Hello" '!'
--ANCHOR_END: pushExplicit


--ANCHOR: push
#eval "Hello".push '!'
--ANCHOR_END: push

#eval "Hello".length

#check "Hello".take 4

#eval "Hello".take 4

#check " Hello  ".trimAscii

#eval " Hello  ".trimAscii

#eval " Hello  ".trimAscii.copy

/-- info: "red " -/
#check_msgs in
--ANCHOR: dropEndWhileFun
#eval ("red admiral".dropEndWhile Char.isAlpha).copy
--ANCHOR_END: dropEndWhileFun

--ANCHOR: dropEndWhileChar
#eval "red admiral".dropEndWhile 'l'
--ANCHOR_END: dropEndWhileChar

--ANCHOR: dropWhileString
#eval "the the butterfly".dropWhile "the "
--ANCHOR_END: dropWhileString

--ANCHOR: dropWhileString2
#eval ("a gray grayling".drop 2).dropWhile "gray "
--ANCHOR_END: dropWhileString2

--ANCHOR: copy
#eval (("small tortoiseshell".drop 6).dropEnd 5).copy
--ANCHOR_END: copy

/--
error: don't know how to synthesize implicit argument `ρ`
  @String.dropEndWhile ?m.2 "red admiral"
context:
⊢ Type
-/
#check_msgs in
--ANCHOR: dropEndWhileNoArg
#eval "red admiral".dropEndWhile
--ANCHOR_END: dropEndWhileNoArg


/--
error: failed to synthesize instance of type class
  String.Slice.Pattern.BackwardPattern [12]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#check_msgs in
--ANCHOR: dropEndWhileListArg
#eval "12345abcde".dropEndWhile [12]
--ANCHOR_END: dropEndWhileListArg
