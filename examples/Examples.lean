import Examples.Utils

def helloWorld : IO Unit :=
  IO.println "Hello, world!"

-- Thoughts:
-- 1. Can we make the default library for stdin/stdout/stderr a bit
--    richer and expose things like flushing? Do we need IO actions to
--    get the stdout and stdin?
-- 2. Why doesn't >> work?
def greetingNoDo : IO Unit :=
  IO.getStdin >>=
    fun stdin => IO.getStdout >>=
      fun stdout => stdout.putStr "What is your name? " >>=
        fun () => stdout.flush >>=
          fun () => stdin.getLine >>=
            fun name => stdout.putStr s!"Hello, {name}!\n"


def greeting : IO Unit := do
  let stdin <- IO.getStdin
  let stdout <- IO.getStdout
  stdout.putStr "What is your name? "
  stdout.flush
  let name <- stdin.getLine
  stdout.putStr s!"Hello, {name}!\n"

def strln : IO Unit := do
  let stdin <- IO.getStdin
  let stdout <- IO.getStdout
  stdout.putStr "Enter a string: "
  stdout.flush
  let str <- stdin.getLine
  stdout.putStrLn s!"It was {str.length} chars"

#eval 1 + 2

#eval String.append "it is " (if 1 > 2 then "yes" else "no")

#eval (1 + 2 : Nat)

#eval 1 - 2

#eval (1 - 2 : Int)

#check (1 - 2 : Int)

#check String.append "hello" [" ", "world"]

namespace RPN

  structure State where
    stack : List Int

  inductive Err where
    | underflow
    | divBy0
    deriving Repr
  open Err

  open Sum

  def Command : Type := State -> Sum Err State

  def push (i : Int) : Command
    | st => inr { stack := i :: st.stack }

  def drop : Command
    | {stack := _::xs} => inr {stack := xs}
    | _ => inl underflow

  def dup : Command
    | {stack := []} => inl underflow
    | {stack := x::xs} => inr {stack := x :: x :: xs}

  def swap : Command
    | {stack := x::y::xs} => inr {stack := y :: x :: xs}
    | {stack := _} => inl underflow

  def bin (op : Int -> Int -> Int) : Command
    | {stack := x::y::xs} => inr {stack := op x y :: xs}
    | {stack := _} => inl underflow

  def plus := bin (fun x y => x + y)
  def minus := bin (fun x y => x - y)
  def times := bin (fun x y => x * y)
  def divide : Command
    | {stack := 0::y::xs} => inl divBy0
    | other => bin (fun x y => x / y) other

  def dump (out : IO.FS.Stream) (state : State) : IO Unit := do
    out.putStrLn s!"Depth: {state.stack.length}"
    for i in state.stack.reverse do
      out.putStrLn s!"\t{i}"

  def getCommand (string : String) : Option Command :=
    push <$> stringToInt string <|>
      (match string with
         | "+" => some plus
         | "-" => some minus
         | "*" => some times
         | "/" => some divide
         | "dup" => some dup
         | "swap" => some swap
         | "drop" => some drop
         | other => none)

  def command (input : IO.FS.Stream) (output : IO.FS.Stream) (state : State) : IO State := do
    dump output state
    output.putStr "> "
    output.flush
    let line := trim (<- input.getLine)
    match getCommand line with
      | none => do output.putStrLn "Didn't understand" ; pure state
      | some cmd =>
        match cmd state with
          | inl err => output.putStrLn (reprStr err) ; pure state
          | inr st' => pure st'


  partial def calculator : IO Unit := do
    let initState  := State.mk []
    let stdin <- IO.getStdin
    let stdout <- IO.getStdout
    let rec loop (st : State) : IO Unit := do
      let st' <- command stdin stdout st
      loop st'
    loop initState

end RPN

def examples : List (String × IO Unit) :=
  [ ("Hello, world", helloWorld),
    ("Greeting", greeting),
    ("String length", strln),
    ("RPN calculator",  RPN.calculator)
  ]
