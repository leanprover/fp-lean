import ExampleSupport

#eval [3] |> List.reverse

namespace PipelineEx

variable (α : Type)
variable (β : Type)
variable (γ : Type)
variable (δ : Type)

variable (E₁ : α)
variable (E₂ : α → β)
variable (E₃ : β → γ)
variable (E₄ : γ → δ)

-- ANCHOR: pipelineShort
example : (
E₁ |> E₂
) = (
E₂ E₁
) := rfl
-- ANCHOR_END: pipelineShort


-- ANCHOR: pipeline
example : (
E₁ |> E₂ |> E₃ |> E₄
) = (
E₄ (E₃ (E₂ E₁))
) := rfl
-- ANCHOR_END: pipeline


/-- info:
"(some 5)"
-/
#check_msgs in
-- ANCHOR: some5
#eval some 5 |> toString
-- ANCHOR_END: some5


-- ANCHOR: times3
def times3 (n : Nat) : Nat := n * 3
-- ANCHOR_END: times3

/-- info:
"It is 15"
-/
#check_msgs in
-- ANCHOR: itIsFive
#eval 5 |> times3 |> toString |> ("It is " ++ ·)
-- ANCHOR_END: itIsFive


/-- info:
"It is 15"
-/
#check_msgs in
-- ANCHOR: itIsAlsoFive
#eval ("It is " ++ ·) <| toString <| times3 <| 5
-- ANCHOR_END: itIsAlsoFive

/-- info:
"It is 15"
-/
#check_msgs in
-- ANCHOR: itIsAlsoFiveParens
#eval ("It is " ++ ·) (toString (times3 5))
-- ANCHOR_END: itIsAlsoFiveParens


end PipelineEx

-- ANCHOR: listReverse
example : (
[1, 2, 3].reverse
) = (
List.reverse [1, 2, 3]
) := rfl
-- ANCHOR_END: listReverse

-- ANCHOR: listReverseDropReverse
example : (
([1, 2, 3].reverse.drop 1).reverse
) = (
[1, 2, 3] |> List.reverse |> List.drop 1 |> List.reverse
) := rfl
-- ANCHOR_END: listReverseDropReverse

-- ANCHOR: listReverseDropReversePipe
example : (
[1, 2, 3] |> List.reverse |> List.drop 1 |> List.reverse
) = (
[1, 2, 3] |>.reverse |>.drop 1 |>.reverse
) := rfl
-- ANCHOR_END: listReverseDropReversePipe


-- ANCHOR: spam
def spam : IO Unit := do
  repeat IO.println "Spam!"
-- ANCHOR_END: spam


def bufsize : USize := 20 * 1024


-- ANCHOR: dump
def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  repeat do
    let buf ← stream.read bufsize
    if buf.isEmpty then break
    stdout.write buf
-- ANCHOR_END: dump

namespace More
-- ANCHOR: dumpWhile
def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  let mut buf ← stream.read bufsize
  while not buf.isEmpty do
    stdout.write buf
    buf ← stream.read bufsize
-- ANCHOR_END: dumpWhile
end More

-- ANCHOR: names
example := ForM
-- ANCHOR_END: names
