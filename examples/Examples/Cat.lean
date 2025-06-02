import ExampleSupport

namespace Str


-- ANCHOR: Stream
structure Stream where
  flush   : IO Unit
  read    : USize → IO ByteArray
  write   : ByteArray → IO Unit
  getLine : IO String
  putStr  : String → IO Unit
  isTty   : BaseIO Bool
-- ANCHOR_END: Stream


end Str

similar datatypes Str.Stream IO.FS.Stream


namespace Original

def bufsize : USize := 20 * 1024

partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args

end Original

namespace Improved
def bufsize : USize := 20 * 1024


-- ANCHOR: dump
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream
-- ANCHOR_END: dump

-- ANCHOR: fileStream
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))
-- ANCHOR_END: fileStream


-- ANCHOR: process
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    dump (← IO.getStdin)
    process exitCode args
  | filename :: args =>
    match (← fileStream ⟨filename⟩) with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args
-- ANCHOR_END: process

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
end Improved

example : Original.bufsize = Improved.bufsize := by rfl

@[simp]
axiom dumpEquals : Original.dump = Improved.dump

@[simp]
theorem fileStreamEquals : Original.fileStream = Improved.fileStream := by rfl

@[simp]
theorem processEqual : Original.process = Improved.process := by
  funext err args; revert err
  induction args with
    | nil =>
      simp [Original.process, Improved.process]
    | cons head tail ih =>
      cases decEq head "-" <;> simp [*, ih, Original.process, Improved.process]

example : Original.main = Improved.main := by
  funext x
  simp [Original.main, Improved.main]





-- ANCHOR: getNumA
def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5
-- ANCHOR_END: getNumA


-- ANCHOR: getNumB
def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 7
-- ANCHOR_END: getNumB

-- ANCHOR: getNums
def getNums (n : Nat) : IO (Nat × Nat) := do
  (← IO.getStdout).putStrLn "Nums"
  pure (n, n+n)
-- ANCHOR_END: getNums


/-- error:
invalid use of `(<- ...)`, must be nested inside a 'do' expression
-/
#check_msgs in
-- ANCHOR: testEffects
def test : IO Unit := do
  let a : Nat := if (← getNumA) == 5 then 0 else (← getNumB)
  (← IO.getStdout).putStrLn s!"The answer is {a}"
-- ANCHOR_END: testEffects


namespace Foo
-- ANCHOR: testEffectsExpanded
def test : IO Unit := do
  let x ← getNumA
  let y ← getNumB
  let a : Nat := if x == 5 then 0 else y
  (← IO.getStdout).putStrLn s!"The answer is {a}"
-- ANCHOR_END: testEffectsExpanded
end Foo


def a : IO Nat := do
  pure ((← getNumA) + (← getNums (← getNumB)).snd)

def b : IO Nat := do
  let x ← getNumA
  let y ← getNumB
  let z ← getNums y
  pure (x + z.snd)

def c : IO Nat := do
  let y ← getNumA
  let x ← getNumB
  let z ← getNums y
  pure (x + z.snd)


def one : IO Nat := pure 1
def two : IO Nat := pure 2

namespace HelloName1
-- ANCHOR: helloOne
-- This version uses only whitespace-sensitive layout
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trim
  stdout.putStrLn s!"Hello, {name}!"
-- ANCHOR_END: helloOne
end HelloName1

namespace HelloName2
-- ANCHOR: helloTwo
-- This version is as explicit as possible
def main : IO Unit := do {
  let stdin ← IO.getStdin;
  let stdout ← IO.getStdout;

  stdout.putStrLn "How would you like to be addressed?";
  let name := (← stdin.getLine).trim;
  stdout.putStrLn s!"Hello, {name}!"
}
-- ANCHOR_END: helloTwo
end HelloName2

namespace HelloName3
-- ANCHOR: helloThree
-- This version uses a semicolon to put two actions on the same line
def main : IO Unit := do
  let stdin ← IO.getStdin; let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trim
  stdout.putStrLn s!"Hello, {name}!"
-- ANCHOR_END: helloThree
end HelloName3

open Nat (toFloat)
#eval toFloat 32
