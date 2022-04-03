
import Examples
import Examples.Utils


def index (cases : List α) : List (Nat × α) :=
  let rec go (n : Nat) opts :=
    match opts with
      | [] => []
      | x :: xs => (n, x) :: go (n + 1) xs;
  go 0 cases

partial def getNat : IO Nat := do
  let stdout <- IO.getStdout
  let stdin <- IO.getStdin
  let str <- stdin.getLine
  match stringToNat (trim str) with
    | none => do
      stdout.putStrLn "Wasn't a number"
      getNat
    | some k => pure k

partial def menu (title : String) (options : List (String × α)) : IO α := do
  let opts := index options
  let stdout <- IO.getStdout
  let stdin <- IO.getStdin
  let rec getOption := do
    stdout.putStrLn title
    for (i, (name, val)) in opts do
      stdout.putStrLn s!"\t{i}. {name}"
    stdout.putStr "> "
    stdout.flush
    let n <- getNat
    match lookup n opts with
      | none => getOption
      | some (_, v) => pure v
  getOption

def main : IO Unit := do
  let ex <- menu "Select an example" examples
  ex
