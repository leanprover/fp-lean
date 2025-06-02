-- ANCHOR: all
-- ANCHOR: sig
def main : IO Unit := do
-- ANCHOR_END: sig
  -- ANCHOR: setup
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  -- ANCHOR_END: setup

  -- ANCHOR: question
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace
  -- ANCHOR_END: question

  -- ANCHOR: answer
  stdout.putStrLn s!"Hello, {name}!"
  -- ANCHOR_END: answer
-- ANCHOR_END: all


def mainSplit : IO Unit := do
  -- ANCHOR: block1
  -- ANCHOR: line1
  let stdin ← IO.getStdin
  -- ANCHOR_END: line1
  -- ANCHOR: block2
  -- ANCHOR: line2
  let stdout ← IO.getStdout
  -- ANCHOR_END: line2
  -- ANCHOR: block3
  -- ANCHOR: line3
  stdout.putStrLn "How would you like to be addressed?"
  -- ANCHOR_END: line3
  -- ANCHOR: block4
  -- ANCHOR: line4
  let input ← stdin.getLine
  -- ANCHOR_END: line4
  -- ANCHOR: block5
  -- ANCHOR: line5
  let name := input.dropRightWhile Char.isWhitespace
  -- ANCHOR_END: line5
  -- ANCHOR: block6
  -- ANCHOR: line6
  stdout.putStrLn s!"Hello, {name}!"
  -- ANCHOR_END: line6
  -- ANCHOR_END: block6
  -- ANCHOR_END: block5
  -- ANCHOR_END: block4
  -- ANCHOR_END: block3
  -- ANCHOR_END: block2
  -- ANCHOR_END: block1

-- Keep checking that they're identical
example : main = mainSplit := by rfl

example := String.dropRightWhile
example {α : Type} := IO α
example : String → IO Unit := IO.println
example := Bool
open Unit in
example : Unit := unit
example := IO.FS.Stream
example : IO.FS.Stream → String → IO Unit := IO.FS.Stream.putStrLn
example : IO.FS.Stream → IO String := IO.FS.Stream.getLine
