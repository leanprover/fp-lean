import Examples.Support

#eval [3] |> List.reverse

namespace PipelineEx

axiom α : Type
axiom β : Type
axiom γ : Type
axiom δ : Type

axiom E1 : α
axiom E2 : α → β
axiom E3 : β → γ
axiom E4 : γ → δ

bookExample {{{ pipelineShort }}}
  E1 |> E2
  ===>
  E2 E1
end bookExample


bookExample {{{ pipeline }}}
  E1 |> E2 |> E3 |> E4
  ===>
  E4 (E3 (E2 E1))
end bookExample


expect info {{{ some5 }}}
  #eval some 5 |> toString
message
"\"(some 5)\""
end expect


book declaration {{{ times3 }}}
  def times3 (n : Nat) : Nat := n * 3
stop book declaration

expect info {{{ itIsFive }}}
  #eval 5 |> times3 |> toString |> ("It is " ++ ·)
message
"\"It is 15\""
end expect


expect info {{{ itIsAlsoFive }}}
  #eval ("It is " ++ ·) <| toString <| times3 <| 5
message
"\"It is 15\""
end expect

expect info {{{ itIsAlsoFiveParens }}}
  #eval ("It is " ++ ·) (toString (times3 5))
message
"\"It is 15\""
end expect


end PipelineEx

bookExample {{{ listReverse }}}
  [1, 2, 3].reverse
  ===>
  List.reverse [1, 2, 3]
end bookExample

bookExample {{{ listReverseDropReverse }}}
  ([1, 2, 3].reverse.drop 1).reverse
  ===>
  [1, 2, 3] |> List.reverse |> List.drop 1 |> List.reverse
end bookExample

bookExample {{{ listReverseDropReversePipe }}}
  [1, 2, 3] |> List.reverse |> List.drop 1 |> List.reverse
  ===>
  [1, 2, 3] |>.reverse |>.drop 1 |>.reverse
end bookExample


book declaration {{{ spam }}}
  def spam : IO Unit := do
    repeat IO.println "Spam!"
stop book declaration


def bufsize : USize := 20 * 1024


book declaration {{{ dump }}}
  def dump (stream : IO.FS.Stream) : IO Unit := do
    let stdout ← IO.getStdout
    repeat do
      let buf ← stream.read bufsize
      if buf.isEmpty then break
      stdout.write buf
stop book declaration

namespace More
book declaration {{{ dumpWhile }}}
  def dump (stream : IO.FS.Stream) : IO Unit := do
    let stdout ← IO.getStdout
    let mut buf ← stream.read bufsize
    while not buf.isEmpty do
      stdout.write buf
      buf ← stream.read bufsize
stop book declaration
end More
