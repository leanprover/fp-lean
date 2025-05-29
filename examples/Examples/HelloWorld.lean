import ExampleSupport
open SubVerso.Examples

-- ANCHOR: MainTypes
discarding
def main : IO Unit := pure ()
stop discarding
discarding
def main : IO UInt32 := pure 0
stop discarding
discarding
def main : List String → IO UInt32 := fun _ => pure 0
stop discarding

-- ANCHOR_END: MainTypes

/-- info:
"Hello"
-/
#check_msgs in
-- ANCHOR: dropBang
#eval "Hello!!!".dropRightWhile (· == '!')
-- ANCHOR_END: dropBang

/-- info:
"Hello"
-/
#check_msgs in
-- ANCHOR: dropNonLetter
#eval "Hello...   ".dropRightWhile (fun c => not (c.isAlphanum))
-- ANCHOR_END: dropNonLetter



-- ANCHOR: twice
def twice (action : IO Unit) : IO Unit := do
  action
  action
-- ANCHOR_END: twice

%show_name twice as twice.name

/--
info: shy
shy
-/
#check_msgs in
-- ANCHOR: twiceShy
#eval twice (IO.println "shy")
-- ANCHOR_END: twiceShy

example := Nat.zero
example := Nat.succ
example := "Hello, David!"
example := "David"
example {α : Type} := IO α

-- ANCHOR: nTimes
def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n
-- ANCHOR_END: nTimes

-- ANCHOR: nTimes3
#eval nTimes (IO.println "Hello") 3
-- ANCHOR_END: nTimes3

example : α → List α → List α := List.cons

-- ANCHOR: countdown
def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n
-- ANCHOR_END: countdown


-- ANCHOR: from5
def from5 : List (IO Unit) := countdown 5
-- ANCHOR_END: from5


/-- info:
6
-/
#check_msgs in
-- ANCHOR: from5length
#eval from5.length
-- ANCHOR_END: from5length
-- ANCHOR: runActions
def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions
-- ANCHOR_END: runActions


-- ANCHOR: main
def main : IO Unit := runActions from5
-- ANCHOR_END: main

-- ANCHOR: countdown5
#eval main
-- ANCHOR_END: countdown5

evaluation steps : IO Unit {{{ evalMain }}}
-- ANCHOR: evalMain
main
===>
runActions from5
===>
runActions (countdown 5)
===>
runActions
  [IO.println "5",
   IO.println "4",
   IO.println "3",
   IO.println "2",
   IO.println "1",
   IO.println "Blast off!"]
===>
do IO.println "5"
   IO.println "4"
   IO.println "3"
   IO.println "2"
   IO.println "1"
   IO.println "Blast off!"
   pure ()
-- ANCHOR_END: evalMain
end evaluation steps

/-- info:
3
2
1
Blast off!
-/
#check_msgs in
-- ANCHOR: evalDoesIO
#eval runActions (countdown 3)
-- ANCHOR_END: evalDoesIO

-- Verify claim in book made about guillemets. The following should work:
def «def» := 5

namespace Exercises
--ANCHOR: ExMain
def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting
--ANCHOR_END: ExMain

  -- Part of a solution
  /-- info:
Bonjour!
Hello!

-/
#check_msgs in
-- ANCHOR: unused
#eval main
  -- ANCHOR_END: unused
end Exercises
