import Std.Data.HashMap

private inductive NormMetavarState where
  /-- Not looking at a metavar -/
  | none
  /-- Saw the leading '?' -/
  | «?» (iter : String.Iterator)
  /-- Saw the '?m' -/
  | «?m» (iter : String.Iterator)
  /-- Saw the '?m.' -/
  | «?m.» (iter : String.Iterator)
  /-- Saw one or more digits - '?m.[0-9]+' -/
  | «?m.[0-9]+» (iter : String.Iterator)

/--
Consistently rewrite all substrings that look like automatic metavariables (e.g "?m.123") so
that they're ?m.1, ?m.2, etc.
-/
def normalizeMetavars (str : String) : String := Id.run do
  let mut out := ""
  let mut iter := str.iter
  let mut gensymCounter := 1
  let mut nums : Std.HashMap String Nat := {}
  let mut state : NormMetavarState := .none
  while h : iter.hasNext do
    let c := iter.curr' h

    match state with
    | .none =>
      if c == '?' then
        state := .«?» iter
      else
        out := out.push c
    | .«?» i =>
      state := if c == 'm' then .«?m» i else .none
    | .«?m» i =>
      state := if c == '.' then .«?m.» i else .none
    | .«?m.» i =>
      state := if c.isDigit then .«?m.[0-9]+» i else .none
    | .«?m.[0-9]+» i =>
      unless c.isDigit do
        state := .none
        let mvarStr := i.extract iter
        match nums[mvarStr]? with
        | none =>
          nums := nums.insert mvarStr gensymCounter
          out := out ++ s!"?m.{gensymCounter}"
          gensymCounter := gensymCounter + 1
        | some s => out := out ++ s!"?m.{s}"
        out := out.push c

    iter := iter.next

  match state with
  | .«?m.[0-9]+» i =>
    let mvarStr := i.extract iter
    match nums[mvarStr]? with
    | none =>
      nums := nums.insert mvarStr gensymCounter
      out := out ++ s!"?m.{gensymCounter}"
      gensymCounter := gensymCounter + 1
    | some s => out := out ++ s!"?m.{s}"
  | .«?» i  | .«?m» i | .«?m.» i =>
    out := out ++ i.extract iter
  | .none => pure ()

  out

/-- info: "List ?m.1" -/
#guard_msgs in
#eval normalizeMetavars "List ?m.9783"

/-- info: "List ?m.1 " -/
#guard_msgs in
#eval normalizeMetavars "List ?m.9783 "

/-- info: "x : ?m.1\nxs : List ?m.1\nelem : x ∈ xs\n⊢ xs.length > 0\n" -/
#guard_msgs in
#eval normalizeMetavars
  r##"x : ?m.1034
xs : List ?m.1034
elem : x ∈ xs
⊢ xs.length > 0
"##

/-- info: "x : ?m.1\nxs : List ?m.1\nelem : x ∈ xs\n⊢ xs.length > 0" -/
#guard_msgs in
#eval normalizeMetavars
  r##"x : ?m.1034
xs : List ?m.1034
elem : x ∈ xs
⊢ xs.length > 0"##

/-- info: "x : ?m.1\nxs : List ?m.2\nelem : x ∈ xs\n⊢ xs.length > 0" -/
#guard_msgs in
#eval normalizeMetavars
  r##"x : ?m.1034
xs : List ?m.10345
elem : x ∈ xs
⊢ xs.length > 0"##

/-- info: "x : ?m.1\nxs : List ?m.2\nelem : x ∈ xs\n⊢ xs.length > 0" -/
#guard_msgs in
#eval normalizeMetavars
  r##"x : ?m.1035
xs : List ?m.1034
elem : x ∈ xs
⊢ xs.length > 0"##

/-- info: "x : ?m.1\nα : Type .1234\nxs : List ?m.2\nelem : x ∈ xs\n⊢ xs.length > 0" -/
#guard_msgs in
#eval normalizeMetavars
  r##"x : ?m.1035
α : Type ?u.1234
xs : List ?m.1034
elem : x ∈ xs
⊢ xs.length > 0"##
