namespace FPLean.Commands.Shell

private inductive State where
  | normal
  | inSingle
  | inDouble
  | escaped (st : State)

def shlex (cmd : String) : Except String (Array String) := do
  let mut state : State := .normal
  let mut iter := cmd.iter
  let mut out : Array String := #[]
  let mut current : Option String := none
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    match state, c with
    | .normal, '\\' =>
      state := .escaped state
    | .normal, '\'' =>
      state := .inSingle
      current := some <| current.getD ""
    | .normal, '"' =>
      state := .inDouble
      current := some <| current.getD ""
    | .normal, ' ' | .normal, '\t' | .normal, '\n' =>
      if let some curr := current then
        out := out.push curr
        current := none
    | .normal, _ =>
      current := current.getD "" |>.push c |> some
    | .escaped s', _ =>
      current := current.getD "" |>.push c |> some
      state := s'
    | .inDouble, '"' =>
      state := .normal
    | .inDouble, '\\' =>
      state := .escaped state
    | .inDouble, _ =>
      current := current.getD "" |>.push c |> some
    | .inSingle, '\'' =>
      state := .normal
    | .inSingle, _ =>
      current := current.getD "" |>.push c |> some
  match state with
  | .inSingle => throw "Unclosed single quote"
  | .inDouble => throw "Unclosed double quote"
  | .escaped _ => throw "Unterminated escape"
  | .normal =>
    if let some curr := current then
      out := out.push curr
    return out

/-! # Tests -/

/-! ## Basic cases -/

/-- info: Except.ok #["ls", "-la"] -/
#guard_msgs in
#eval shlex "ls -la"

/-- info: Except.ok #[] -/
#guard_msgs in
#eval shlex ""

/-- info: Except.ok #[] -/
#guard_msgs in
#eval shlex "   "

/-! ## Quote handling -/

/-- info: Except.ok #["echo", "dont"] -/
#guard_msgs in
#eval shlex "echo 'don''t'"

/-- info: Except.ok #["echo", "don't"] -/
#guard_msgs in
#eval shlex "echo \"don't\""

/-- info: Except.ok #["echo", "don\"t"] -/
#guard_msgs in
#eval shlex "echo 'don\"t'"

/-- info: Except.ok #["echo", "\"quoted\""] -/
#guard_msgs in
#eval shlex "echo \"\\\"quoted\\\"\""

/-- info: Except.ok #["echo", ""] -/
#guard_msgs in
#eval shlex "echo ''"

/-- info: Except.ok #["echo", ""] -/
#guard_msgs in
#eval shlex "echo \"\""

/-! ## Escaping -/

/-- info: Except.ok #["echo", "a b"] -/
#guard_msgs in
#eval shlex "echo a\\ b"

/-- info: Except.ok #["echo", "\"quoted\""] -/
#guard_msgs in
#eval shlex "echo \\\"quoted\\\""

/-- info: Except.ok #["echo", "\\"] -/
#guard_msgs in
#eval shlex "echo \\\\"

/-- info: Except.ok #["echo", "\\\\"] -/
#guard_msgs in
#eval shlex "echo \\\\\\\\"

/-- info: Except.ok #["echo", "a\\b"] -/
#guard_msgs in
#eval shlex "echo a\\\\b"

/-- info: Except.ok #["echo", "a\nb"] -/
#guard_msgs in
#eval shlex "echo a\\\nb"


/-! ## Mixed quotes and escapes -/

/-- info: Except.ok #["echo", "mixed 'quotes'"] -/
#guard_msgs in
#eval shlex "echo \"mixed 'quotes'\""

/-- info: Except.ok #["echo", "mixed \"quotes\""] -/
#guard_msgs in
#eval shlex "echo 'mixed \"quotes\"'"

/-- info: Except.ok #["echo", "partially quoted argument"] -/
#guard_msgs in
#eval shlex "echo \"partially quoted\\ argument\""

/-- info: Except.ok #["echo", "ends with backslash\\"] -/
#guard_msgs in
#eval shlex "echo \"ends with backslash\\\\\""

/-- info: Except.ok #["echo", "single quoted string with \\ backslash"] -/
#guard_msgs in
#eval shlex "echo 'single quoted string with \\ backslash'"

/-! ## Whitespace-/

/-- info: Except.ok #["cmd", "with", "multiple", "spaces"] -/
#guard_msgs in
#eval shlex "cmd  with  multiple    spaces"

/-- info: Except.ok #["cmd", "with", "tabs"] -/
#guard_msgs in
#eval shlex "cmd\twith\ttabs"

/-- info: Except.ok #["cmd", "with", "newlines"] -/
#guard_msgs in
#eval shlex "cmd with\nnewlines"

/-! ## Complex combinations -/

/-- info: Except.ok #["echo", "foobar"] -/
#guard_msgs in
#eval shlex "echo \"foo\"'bar'"

/-- info: Except.ok #["echo", "foobar"] -/
#guard_msgs in
#eval shlex "echo \"foo\"\"bar\""

/-- info: Except.ok #["grep", "term with spaces", "file with spaces.txt"] -/
#guard_msgs in
#eval shlex "grep \"term with spaces\" file\\ with\\ spaces.txt"

/-- info: Except.ok #["echo", "-n", "mixed \"quotes\" and 'apostrophes'"] -/
#guard_msgs in
#eval shlex "echo -n \"mixed \\\"quotes\\\" and 'apostrophes'\""

/-- info: Except.ok #["find", ".", "-name", "*{1,2}*"] -/
#guard_msgs in
#eval shlex "find . -name \"*\\{1,2\\}*\""

/-! ## Potentially problematic edge cases -/


/-- info: Except.error "Unterminated escape" -/
#guard_msgs in
#eval shlex "\\"

/-- info: Except.ok #["cmd", "with", "trailing", "space"] -/
#guard_msgs in
#eval shlex "cmd with trailing space "

/-- info: Except.ok #["cmd", "with", "trailing", "escaped", "space "] -/
#guard_msgs in
#eval shlex "cmd with trailing escaped space\\ "

/-- info: Except.ok #["echo", "foo#bar"] -/
#guard_msgs in
#eval shlex "echo foo#bar"

/-- info: Except.ok #["echo", "fooz"] -/
#guard_msgs in
#eval shlex "echo \"foo\\z\""

/-! ## Tricky error cases -/

/-- info: Except.error "Unclosed double quote" -/
#guard_msgs in
#eval shlex "echo \"unterminated"

/-- info: Except.error "Unclosed single quote" -/
#guard_msgs in
#eval shlex "echo 'unterminated"

/-- info: Except.error "Unterminated escape" -/
#guard_msgs in
#eval shlex "echo \\"

/-- info: Except.ok #["echo", "nested quotes"] -/
#guard_msgs in
#eval shlex "echo \"nested \"quotes\"\""

/-! ## Boundary cases -/

/-- info: Except.ok #["ab"] -/
#guard_msgs in
#eval shlex "a\"\"b"

/-- info: Except.ok #["ab"] -/
#guard_msgs in
#eval shlex "a''b"

/-- info: Except.ok #["ab"] -/
#guard_msgs in
#eval shlex "\"a\"\"b\""

/-- info: Except.ok #["ab"] -/
#guard_msgs in
#eval shlex "'a''b'"
