-- ANCHOR: main
def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  unless argv == [] do
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    return 1

  stdout.putStrLn "How would you like to be addressed?"
  stdout.flush

  let name := (← stdin.getLine).trim
  if name == "" then
    stderr.putStrLn s!"No name provided"
    return 1

  stdout.putStrLn s!"Hello, {name}!"

  return 0
-- ANCHOR_END: main

namespace Nested
-- ANCHOR: nestedmain
def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  if argv != [] then
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    pure 1
  else
    stdout.putStrLn "How would you like to be addressed?"
    stdout.flush

    let name := (← stdin.getLine).trim
    if name == "" then
      stderr.putStrLn s!"No name provided"
      pure 1
    else
      stdout.putStrLn s!"Hello, {name}!"
      pure 0
-- ANCHOR_END: nestedmain
end Nested

theorem mains_match : main = Nested.main := by
  funext argv
  simp [main, Nested.main]
  simp [bind, EStateM.bind, EStateM.pure, liftM, monadLift, pure, ite]
  funext s
  repeat split <;> try simp_all
  cases argv <;>
    simp [instDecidableEqString, instDecidableEqList, List.hasDecEq, bne, BEq.beq, List.beq, not, instDecidableEqBool, Bool.decEq, IO.FS.Stream.putStrLn, IO.FS.Stream.putStr, String.push, String.decEq, String.trim, instDecidableNot, *]
