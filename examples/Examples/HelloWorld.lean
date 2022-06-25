import Examples.Support

expect info {{{ dropBang }}}
  #eval "Hello!!!".dropRightWhile (· == '!')
message
  "\"Hello\"
"
end expect

expect info {{{ dropNonLetter }}}
  #eval "Hello...   ".dropRightWhile (fun c => not (c.isAlphanum))
message
"\"Hello\"
"
end expect



book declaration {{{ twice }}}
def twice (action : IO Unit) : IO Unit := do
  action
  action
stop book declaration

expect eval info {{{ twiceShy }}}
  twice (IO.println "shy")
message
"shy
shy
"
end expect



book declaration {{{ nTimes }}}
def nTimes (action : IO Unit) : Nat → IO Unit
  | Nat.zero => pure ()
  | Nat.succ n => do
    action
    nTimes action n
stop book declaration

expect eval info {{{ nTimes3 }}}
  nTimes (IO.println "Hello") 3
message
"Hello
Hello
Hello
"
end expect

book declaration {{{ countdown }}}
  def countdown : Nat → List (IO Unit)
    | Nat.zero => [IO.println "Blast off!"]
    | Nat.succ n => IO.println s!"{n+1}" :: countdown n
stop book declaration


book declaration {{{ from5 }}}
  def from5 : List (IO Unit) := countdown 5
stop book declaration


expect info {{{ from5length }}}
  #eval from5.length
message
"6
"
end expect
book declaration {{{ runActions }}}
  def runActions : List (IO Unit) → IO Unit
    | [] => pure ()
    | act :: actions => do
      act
      runActions actions
stop book declaration


book declaration {{{ main }}}
  def main : IO Unit := runActions from5
stop book declaration

expect eval info {{{ countdown5 }}}
  main
message
"5
4
3
2
1
Blast off!
"
end expect

evaluation steps : IO Unit {{{ evalMain }}}
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
end evaluation steps
