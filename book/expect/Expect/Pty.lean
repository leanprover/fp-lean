/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public section

/-!
Child processes running on a pseudoterminal.

A terminal makes programs behave as they do for a person at a keyboard: output is line buffered,
input is echoed back as it is sent, and standard output and standard error arrive interleaved in
the order they were written.
-/

namespace Expect.Pty

private opaque ChildPointed : NonemptyType

/--
A child process, together with the controlling end of its terminal.

Releasing the last reference to a child closes its terminal, and terminates the process if it is
still running.
-/
def Child : Type := ChildPointed.type

instance : Nonempty Child := ChildPointed.property

/--
Starts a command on a new pseudoterminal, in the given working directory.

The child's environment is the current one, with the names in `envUnset` removed and the
`"NAME=VALUE"` entries of `envOverrides` added. The command is looked up on the `PATH` that
results.
-/
@[extern "expect_pty_spawn"]
private opaque spawnRaw (argv : @& Array String) (envOverrides : @& Array String)
    (envUnset : @& Array String) (cwd : @& String) : IO Child

/-- Whether the child has produced output, waiting up to `timeoutMs` for some to arrive. -/
@[extern "expect_pty_poll"]
opaque Child.ready (child : @& Child) (timeoutMs : UInt32) : IO Bool

/-- Reads what the child has produced. The result is empty once the terminal has closed. -/
@[extern "expect_pty_read"]
opaque Child.readBytes (child : @& Child) (max : UInt32) : IO ByteArray

@[extern "expect_pty_write"]
private opaque writeRaw (child : @& Child) (bytes : @& ByteArray) (timeoutMs : UInt32) : IO Unit

/--
Sends the character that ends the child's input, taking up to `timeoutMs`.

The terminal shows nothing for it, so a transcript holds only what the program wrote and what was
typed for it to read.
-/
@[extern "expect_pty_write_eof"]
opaque Child.writeEOF (child : @& Child) (timeoutMs : UInt32) : IO Unit

/-- The child's exit code, or `none` if it is still running after `timeoutMs`. -/
@[extern "expect_pty_wait"]
opaque Child.wait (child : @& Child) (timeoutMs : UInt32) : IO (Option UInt32)

/-- Terminates the child and reaps it. -/
@[extern "expect_pty_kill"]
opaque Child.kill (child : @& Child) : IO Unit

/-- Releases the terminal. -/
@[extern "expect_pty_close"]
opaque Child.close (child : @& Child) : IO Unit

/-- Starts a command on a new pseudoterminal, in the given working directory. -/
def Child.spawn (cmd : String) (args : Array String) (cwd : System.FilePath)
    (envOverrides : Array String := #[]) (envUnset : Array String := #[]) : IO Child :=
  spawnRaw (#[cmd] ++ args) envOverrides envUnset cwd.toString

/-- Reads what the child has produced. The result is empty once the terminal has closed. -/
def Child.read (child : Child) (max : UInt32 := 4096) : IO ByteArray :=
  child.readBytes max

/-- Sends text to the child as if it had been typed, taking up to `timeoutMs` altogether. -/
def Child.write (child : Child) (text : String) (timeoutMs : UInt32 := 1500) : IO Unit :=
  writeRaw child text.toUTF8 timeoutMs
