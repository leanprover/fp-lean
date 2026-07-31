/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public section

/-!
Output received from a program, as it arrives.

A read returns whatever bytes happen to be available, which may stop partway through a character,
so received bytes are decoded as far as they go and the rest is kept for the next read.
-/

namespace Expect

/--
Output that has been received but not yet used.

Bytes at the end that do not yet form a whole character are kept apart until the rest of that
character arrives.
-/
structure Buffer where
  /-- The text received so far. -/
  text : String := ""
  /-- Bytes of a character whose remaining bytes have not arrived. There are at most three. -/
  incomplete : ByteArray := .empty
  /-- Whether a carriage return has arrived whose following character has not. -/
  heldReturn : Bool := false
deriving Inhabited

/--
The number of bytes at the end that begin a character whose remaining bytes have not arrived yet.

A character is at most four bytes long, and every byte after the first has `10` as its two high
bits, so only the last three bytes can belong to an unfinished character.
-/
private def incompleteSuffix (bytes : ByteArray) : Nat := Id.run do
  for back in [1, 2, 3] do
    if back ≤ bytes.size then
      let b := bytes.get! (bytes.size - back)
      unless b &&& 0xc0 == 0x80 do
        let width :=
          if b &&& 0x80 == 0x00 then 1
          else if b &&& 0xe0 == 0xc0 then 2
          else if b &&& 0xf0 == 0xe0 then 3
          else if b &&& 0xf8 == 0xf0 then 4
          else 1
        return if back < width then back else 0
  return 0

/--
Adds received bytes, decoding as many of them as form whole characters.

The result is `none` when the bytes are not text at all. A terminal writes a carriage return before
each newline, and each such pair becomes a newline here. A carriage return at the very end is held
back until the character after it arrives, so that a pair split across two reads is recognized.
-/
def Buffer.push (buffer : Buffer) (bytes : ByteArray) : Option Buffer := do
  let received := buffer.incomplete ++ bytes
  let whole := received.size - incompleteSuffix received
  let text ← String.fromUTF8? (received.extract 0 whole)
  let text := (if buffer.heldReturn then "\r" else "") ++ text
  let text := text.replace "\r\n" "\n"
  let heldReturn := text.endsWith "\r"
  return {
    text := buffer.text ++ (if heldReturn then text.dropEnd 1 else text)
    incomplete := received.extract whole received.size
    heldReturn
  }

/-- Whether no text is waiting to be used. -/
def Buffer.isEmpty (buffer : Buffer) : Bool :=
  buffer.text.isEmpty && !buffer.heldReturn

/-- All of the text received, leaving only any unfinished character behind. -/
def Buffer.flush (buffer : Buffer) : String × Buffer :=
  (buffer.text ++ (if buffer.heldReturn then "\r" else ""),
   { buffer with text := "", heldReturn := false })

/--
The text up to the first occurrence of `pattern`, and what is left once that text and the
occurrence itself have been used, or `none` if the pattern has not been received.
-/
def Buffer.take (buffer : Buffer) (pattern : String) : Option (String × Buffer) := do
  let text := buffer.text
  let found ← text.find? pattern
  let before := (text.sliceTo found)
  let rest := (text.sliceFrom found).dropPrefix pattern
  return (before.copy, { buffer with text := rest.copy })

section Tests

private def bytes (s : String) : ByteArray := s.toUTF8

-- Text arrives as text
#guard ((Buffer.push {} (bytes "Hello")).map (·.text)) == some "Hello"

-- A character split across reads is held back until the rest of it arrives
#guard
  let split := "é".toUTF8
  let first := (Buffer.push {} (split.extract 0 1)).get!
  let second := (first.push (split.extract 1 2)).get!
  first.text.isEmpty && first.incomplete.size == 1 &&
    second.text == "é" && second.incomplete.isEmpty

-- A four-byte character split across three reads
#guard
  let split := "🐛".toUTF8
  let steps := [split.extract 0 1, split.extract 1 3, split.extract 3 4]
  let whole := steps.foldl (fun b part => (b.push part).get!) ({} : Buffer)
  whole.text == "🐛" && whole.incomplete.isEmpty

-- The carriage return that a terminal writes before each newline is dropped
#guard ((Buffer.push {} (bytes "one\r\ntwo\r\n")).map (·.text)) == some "one\ntwo\n"

-- A carriage return and the newline after it are recognized across two reads
#guard
  let first := (Buffer.push {} (bytes "one\r")).get!
  ((first.push (bytes "\ntwo"))).map (·.text) == some "one\ntwo"

-- A carriage return that a program writes on its own is kept
#guard ((Buffer.push {} (bytes "50%\r99%\r")).map (·.flush.1)) == some "50%\r99%\r"

-- A newline that a program writes itself reaches the terminal as two carriage returns, and the
-- one that the program wrote survives however the reads are divided
#guard ((Buffer.push {} (bytes "one\r\r\ntwo")).map (·.text)) == some "one\r\ntwo"
#guard
  let first := (Buffer.push {} (bytes "one\r\r\n")).get!
  ((first.push (bytes "two"))).map (·.text) == some "one\r\ntwo"

-- Bytes that are not text at all are reported
#guard (Buffer.push {} ⟨#[0xff, 0xfe, 0x41]⟩).isNone

-- Taking a pattern yields what came before it, and uses up the pattern itself
#guard
  let buffer := (Buffer.push {} (bytes "Name? David\nHello")).get!
  match buffer.take "? " with
  | some (before, rest) => before == "Name" && rest.text == "David\nHello"
  | none => false

-- A pattern that has not been received yet is not taken
#guard ((Buffer.push {} (bytes "Nam")).get!.take "Name").isNone

-- Flushing yields everything received, and keeps any unfinished character
#guard
  let buffer := (Buffer.push {} (bytes "done\n" ++ "é".toUTF8.extract 0 1)).get!
  let (text, rest) := buffer.flush
  text == "done\n" && rest.isEmpty && rest.incomplete.size == 1

end Tests
