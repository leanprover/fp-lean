-- ANCHOR: bufsize
def bufsize : USize := 20 * 1024
-- ANCHOR_END: bufsize

-- ANCHOR: dump
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  let done ← stream.isEof
  if done then
    pure ()
  else
    let buf ← stream.read bufsize
    stdout.write buf
    dump stream
-- ANCHOR_END: dump

-- ANCHOR: fileStream
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
    let fileExists ← filename.pathExists
    if not fileExists then
      let stderr ← IO.getStderr
      stderr.putStrLn s!"File not found: {filename}"
      pure none
    else
      let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
      pure (some (IO.FS.Stream.ofHandle handle))
-- ANCHOR_END: fileStream

-- ANCHOR: process
def process (err : UInt32) (args : List String) : IO UInt32 := do
  match args with
    | [] => pure err
    | "-" :: args =>
      let stdin ← IO.getStdin
      dump stdin
      process err args
    | filename :: args =>
      let stream ← fileStream ⟨filename⟩
      match stream with
        | none =>
          process 1 args
        | some stream =>
          dump stream
          process err args
-- ANCHOR_END: process

-- ANCHOR: main
def main (args : List String) : IO UInt32 :=
  match args with
    | [] => process 0 ["-"]
    | _ =>  process 0 args
-- ANCHOR_END: main
