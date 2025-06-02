-- ANCHOR: bufsize
def bufsize : USize := 20 * 1024
-- ANCHOR_END: bufsize

-- ANCHOR: dump
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    -- ANCHOR: stdoutBind
    let stdout ← IO.getStdout
    stdout.write buf
    -- ANCHOR_END: stdoutBind
    dump stream
-- ANCHOR_END: dump

-- ANCHOR: fileStream
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  -- ANCHOR: fileExistsBind
  let fileExists ← filename.pathExists
  if not fileExists then
  -- ANCHOR_END: fileExistsBind
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))
-- ANCHOR_END: fileStream

-- ANCHOR: Names
section
open IO.FS
#check Stream
open System
#check FilePath

namespace Main1
def main : IO Unit := pure ()
end Main1
namespace Main2
def main : IO UInt32 := pure 0
end Main2
namespace Main3
def main : List String → IO UInt32 := fun _ => pure 0
end Main3

end
-- ANCHOR_END: Names

-- ANCHOR: process
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
-- ANCHOR_END: process

-- ANCHOR: main
def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
-- ANCHOR_END: main

example := USize
